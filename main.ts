// tiny-stack-vm: an interpreter for make.fun's tiny stack ISA v1 (ISA.md in the kit).
// For each /input/<id>/program.bin (+ input.bin) it writes /output/<id>/stdout.bin and exit.txt.
import { existsSync, mkdirSync, readFileSync, readdirSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const OUT_MAX = 65536;

// Immediate size, pops and pushes per opcode; undefined = unknown opcode.
const IMM = new Int8Array(256).fill(-1);
const POPS = new Uint8Array(256);
const PUSH = new Uint8Array(256);
const def = (ops: number[], imm: number, pops: number, push: number) => {
  for (const o of ops) { IMM[o] = imm; POPS[o] = pops; PUSH[o] = push; }
};
def([0x00, 0x30, 0x33, 0x34], 0, 0, 0);
IMM[0x30] = IMM[0x33] = 2;
def([0x01], 1, 0, 1);
def([0x02], 4, 0, 1);
def([0x03, 0x50, 0x51, 0x53], 0, 1, 0);
def([0x04], 0, 1, 2);
def([0x05], 0, 2, 2);
def([0x06], 0, 2, 3);
def([0x07], 0, 3, 3);
def([0x10, 0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x18, 0x19, 0x1a, 0x1c, 0x1d, 0x1e, 0x20, 0x21, 0x22], 0, 2, 1);
def([0x17, 0x1b, 0x40], 0, 1, 1);
def([0x31, 0x32], 2, 1, 0);
def([0x41], 0, 2, 0);
def([0x52], 0, 0, 1);

function run(p: Uint8Array, inp: Uint8Array): [Uint8Array, number] {
  const n = p.length;
  const D = new Int32Array(257);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(OUT_MAX);
  let sp = 0, csp = 0, olen = 0, ip = 0, pc = 0, steps = 0;
  const res = (code: number): [Uint8Array, number] => [out.slice(0, olen), code];
  for (;;) {
    if (steps === 1000000) return res(10);
    if (pc < 0 || pc >= n) return res(9);
    const op = p[pc];
    const imm = IMM[op];
    if (imm < 0) return res(5);
    if (pc + imm >= n) return res(9);
    steps++;
    if (sp < POPS[op]) return res(2);
    if (sp - POPS[op] + PUSH[op] > 256) return res(3);
    const nx = pc + 1 + imm;
    pc = nx;
    let a: number, b: number;
    switch (op) {
      case 0x00: return res(0);
      case 0x01: D[sp++] = (p[nx - 1] << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]; sp++; break;
      case 0x05: a = D[sp - 1]; D[sp - 1] = D[sp - 2]; D[sp - 2] = a; break;
      case 0x06: D[sp] = D[sp - 2]; sp++; break;
      case 0x07: a = D[sp - 3]; D[sp - 3] = D[sp - 2]; D[sp - 2] = D[sp - 1]; D[sp - 1] = a; break;
      case 0x17: D[sp - 1] = -D[sp - 1] | 0; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]; break;
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: {
        b = D[sp - 1]; a = D[sp - 2];
        let r = 0;
        if (op >= 0x13 && op <= 0x16 && b === 0) return res(4);
        switch (op) {
          case 0x10: r = (a + b) | 0; break;
          case 0x11: r = (a - b) | 0; break;
          case 0x12: r = Math.imul(a, b); break;
          case 0x13: r = a === -2147483648 && b === -1 ? a : (a / b) | 0; break;
          case 0x14: r = b === -1 ? 0 : (a % b) | 0; break;
          case 0x15: r = Math.floor((a >>> 0) / (b >>> 0)) | 0; break;
          case 0x16: r = ((a >>> 0) % (b >>> 0)) | 0; break;
          case 0x18: r = a & b; break;
          case 0x19: r = a | b; break;
          case 0x1a: r = a ^ b; break;
          case 0x1c: r = a << (b & 31); break;
          case 0x1d: r = a >> (b & 31); break;
          case 0x1e: r = (a >>> (b & 31)) | 0; break;
          case 0x20: r = a === b ? 1 : 0; break;
          case 0x21: r = a < b ? 1 : 0; break;
          case 0x22: r = a >>> 0 < b >>> 0 ? 1 : 0; break;
        }
        D[sp - 2] = r; sp--;
        break;
      }
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) { const v = D[--sp]; take = op === 0x31 ? v === 0 : v !== 0; }
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return res(7);
        C[csp++] = nx;
        pc = p[nx - 2] | (p[nx - 1] << 8);
        break;
      case 0x34:
        if (csp === 0) return res(8);
        pc = C[--csp];
        break;
      case 0x40:
        a = D[sp - 1];
        if (a < 0 || a > 255) return res(6);
        D[sp - 1] = M[a];
        break;
      case 0x41:
        a = D[sp - 1];
        if (a < 0 || a > 255) return res(6);
        M[a] = D[sp - 2]; sp -= 2;
        break;
      case 0x50: {
        const s = String(D[sp - 1]);
        if (olen + s.length > OUT_MAX) return res(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > OUT_MAX) return res(11);
        out[olen++] = D[--sp] & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++] : -1; break;
      case 0x53: return res(D[--sp] & 255);
    }
  }
}

const read = (f: string) => (existsSync(f) ? new Uint8Array(readFileSync(f)) : new Uint8Array(0));
for (const id of readdirSync(I).sort()) {
  const d = join(O, id);
  mkdirSync(d, { recursive: true });
  let r: [Uint8Array, number];
  try { r = run(read(join(I, id, 'program.bin')), read(join(I, id, 'input.bin'))); }
  catch { r = [new Uint8Array(0), 0]; }
  writeFileSync(join(d, 'stdout.bin'), r[0]);
  writeFileSync(join(d, 'exit.txt'), r[1] + '\n');
}
