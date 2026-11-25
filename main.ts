// Tiny stack VM for make.fun's tiny stack ISA v1: for every instance in the
// input dir, run program.bin on input.bin, write its output bytes to
// stdout.bin and its exit code to exit.txt in the output dir.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const INPUT_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUTPUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';

/** Runs one program to its end: its output bytes and its exit code. */
function run(prog: Uint8Array, input: Uint8Array): { bytes: Uint8Array; code: number } {
  const n = prog.length;
  const S = new Int32Array(256); // data stack
  const C = new Int32Array(64); // call stack
  const M = new Int32Array(256); // memory, all zero
  const out = new Uint8Array(65536);
  let sp = 0, cp = 0, olen = 0, ipos = 0, pc = 0, steps = 0;
  const done = (code: number): { bytes: Uint8Array; code: number } => ({ bytes: out.slice(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = prog[pc];
    steps++;
    switch (op) {
      case 0x00: return done(0); // HALT
      case 0x01: // PUSH8, sign-extended byte
        if (pc + 1 >= n) return done(9);
        if (sp === 256) return done(3);
        S[sp++] = (prog[pc + 1] << 24) >> 24; pc += 2; break;
      case 0x02: // PUSH32, little-endian signed word
        if (pc + 4 >= n) return done(9);
        if (sp === 256) return done(3);
        S[sp++] = prog[pc + 1] | (prog[pc + 2] << 8) | (prog[pc + 3] << 16) | (prog[pc + 4] << 24); pc += 5; break;
      case 0x03: // POP
        if (sp < 1) return done(2);
        sp--; pc++; break;
      case 0x04: // DUP
        if (sp < 1) return done(2);
        if (sp === 256) return done(3);
        S[sp] = S[sp - 1]; sp++; pc++; break;
      case 0x05: { // SWAP
        if (sp < 2) return done(2);
        const t = S[sp - 1]; S[sp - 1] = S[sp - 2]; S[sp - 2] = t; pc++; break; }
      case 0x06: // OVER
        if (sp < 2) return done(2);
        if (sp === 256) return done(3);
        S[sp] = S[sp - 2]; sp++; pc++; break;
      case 0x07: { // ROT: ( a b c -- b c a )
        if (sp < 3) return done(2);
        const a = S[sp - 3]; S[sp - 3] = S[sp - 2]; S[sp - 2] = S[sp - 1]; S[sp - 1] = a; pc++; break; }
      case 0x10: case 0x11: case 0x12: case 0x13: case 0x14: case 0x15: case 0x16:
      case 0x18: case 0x19: case 0x1a: case 0x1c: case 0x1d: case 0x1e:
      case 0x20: case 0x21: case 0x22: { // binary ops: ( a b -- r ), b on top
        if (sp < 2) return done(2);
        const a = S[sp - 2], b = S[sp - 1];
        let r: number;
        if (op === 0x10) r = (a + b) | 0;
        else if (op === 0x11) r = (a - b) | 0;
        else if (op === 0x12) r = Math.imul(a, b); // low 32 bits of the product
        else if (op === 0x13) { // DIV, truncated toward zero
          if (b === 0) return done(4);
          r = a === -2147483648 && b === -1 ? a : (a / b) | 0; }
        else if (op === 0x14) { // MOD, sign of a
          if (b === 0) return done(4);
          r = b === -1 ? 0 : (a % b) | 0; }
        else if (op === 0x15) { // DIVU, unsigned quotient read back signed
          if (b === 0) return done(4);
          const au = a >>> 0, bu = b >>> 0;
          r = ((au - (au % bu)) / bu) | 0; }
        else if (op === 0x16) { // MODU
          if (b === 0) return done(4);
          r = ((a >>> 0) % (b >>> 0)) | 0; }
        else if (op === 0x18) r = a & b;
        else if (op === 0x19) r = a | b;
        else if (op === 0x1a) r = a ^ b;
        else if (op === 0x1c) r = a << (b & 31);
        else if (op === 0x1d) r = a >> (b & 31); // arithmetic
        else if (op === 0x1e) r = (a >>> (b & 31)) | 0; // logical
        else if (op === 0x20) r = a === b ? 1 : 0;
        else if (op === 0x21) r = a < b ? 1 : 0; // signed
        else r = (a >>> 0) < (b >>> 0) ? 1 : 0; // unsigned
        S[sp - 2] = r; sp--; pc++; break; }
      case 0x17: // NEG
        if (sp < 1) return done(2);
        S[sp - 1] = (-S[sp - 1]) | 0; pc++; break;
      case 0x1b: // NOT
        if (sp < 1) return done(2);
        S[sp - 1] = ~S[sp - 1]; pc++; break;
      case 0x30: case 0x31: case 0x32: { // JMP / JZ / JNZ, signed 16-bit offset
        if (pc + 2 >= n) return done(9);
        const rel = ((prog[pc + 1] | (prog[pc + 2] << 8)) << 16) >> 16;
        let take = true;
        if (op !== 0x30) {
          if (sp < 1) return done(2);
          const v = S[--sp];
          take = op === 0x31 ? v === 0 : v !== 0;
        }
        pc = take ? pc + 3 + rel : pc + 3; break; }
      case 0x33: // CALL, unsigned 16-bit address
        if (pc + 2 >= n) return done(9);
        if (cp === 64) return done(7);
        C[cp++] = pc + 3; pc = prog[pc + 1] | (prog[pc + 2] << 8); break;
      case 0x34: // RET
        if (cp === 0) return done(8);
        pc = C[--cp]; break;
      case 0x40: { // LOAD
        if (sp < 1) return done(2);
        const addr = S[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        S[sp - 1] = M[addr]; pc++; break; }
      case 0x41: { // STORE: ( v addr -- )
        if (sp < 2) return done(2);
        const addr = S[sp - 1];
        if (addr < 0 || addr > 255) return done(6);
        M[addr] = S[sp - 2]; sp -= 2; pc++; break; }
      case 0x50: { // PRINT: decimal ASCII, no padding, no newline
        if (sp < 1) return done(2);
        const s = String(S[sp - 1]);
        if (olen + s.length > 65536) return done(11); // writes none of it
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        sp--; pc++; break; }
      case 0x51: // PUTC: one byte, v AND 255
        if (sp < 1) return done(2);
        if (olen === 65536) return done(11);
        out[olen++] = S[--sp] & 255; pc++; break;
      case 0x52: // IN: next input byte, -1 once input is used up
        if (sp === 256) return done(3);
        S[sp++] = ipos < input.length ? input[ipos++] : -1; pc++; break;
      case 0x53: // EXIT: code v AND 255
        if (sp < 1) return done(2);
        return done(S[sp - 1] & 255);
      default: return done(5); // a byte no opcode names
    }
  }
}

for (const id of readdirSync(INPUT_DIR).sort()) {
  const r = run(readFileSync(join(INPUT_DIR, id, 'program.bin')), readFileSync(join(INPUT_DIR, id, 'input.bin')));
  mkdirSync(join(OUTPUT_DIR, id), { recursive: true });
  writeFileSync(join(OUTPUT_DIR, id, 'stdout.bin'), r.bytes);
  writeFileSync(join(OUTPUT_DIR, id, 'exit.txt'), r.code + '\n');
}
