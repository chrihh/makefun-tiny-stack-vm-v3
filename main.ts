// Tiny stack VM, third implementation: a closure handler table. Each opcode
// owns a function in a dispatch array; the loop validates step / pc / opcode /
// immediate rules, then calls the handler. Values live as raw unsigned bits
// in a Uint32Array stack and memory (signed views via | 0 at the point of
// use), return addresses in a Uint16Array, and output gathers as a latin1
// string converted to bytes once at the end. Traps are return codes, never
// exceptions: a handler returns the exit code to finish, or nothing to go on.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const IN_DIR = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT_DIR = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
type Done = number | undefined;

function runVM(prog: Uint8Array, inp: Uint8Array): { out: Buffer; code: number } {
  const n = prog.length;
  const stack = new Uint32Array(256), mem = new Uint32Array(256), rets = new Uint16Array(64);
  let sp = 0, csp = 0, pc = 0, steps = 0, cursor = 0, olen = 0;
  let text = '';
  const finish = (code: number) => ({ out: Buffer.from(text, 'latin1'), code });
  const at = (next: number, back: number): number => prog[next - back];
  const rel16 = (next: number): number => ((at(next, 2) | (at(next, 1) << 8)) << 16) >> 16;
  const H: ((next: number) => Done)[] = new Array(256);
  const push = (v: number): Done => { if (sp >= 256) return 3; stack[sp++] = v; };
  const need = (k: number): Done => (sp < k ? 2 : undefined);
  // Two-argument instructions, registered from one list of operations.
  const bin = (op: number, f: (a: number, b: number) => number, div?: boolean): void => {
    H[op] = () => {
      const bad = need(2); if (bad !== undefined) return bad;
      const b = stack[sp - 1] | 0, a = stack[sp - 2] | 0;
      if (div && b === 0) return 4;
      sp--; stack[sp - 1] = f(a, b);
    };
  };
  bin(0x10, (a, b) => (a + b) | 0);
  bin(0x11, (a, b) => (a - b) | 0);
  bin(0x12, (a, b) => Math.imul(a, b));
  bin(0x13, (a, b) => (a === -2147483648 && b === -1 ? a : (a / b) | 0), true);
  bin(0x14, (a, b) => (b === -1 ? 0 : (a % b) | 0), true);
  bin(0x15, (a, b) => Math.floor((a >>> 0) / (b >>> 0)) | 0, true);
  bin(0x16, (a, b) => ((a >>> 0) % (b >>> 0)) | 0, true);
  bin(0x18, (a, b) => a & b);
  bin(0x19, (a, b) => a | b);
  bin(0x1a, (a, b) => a ^ b);
  bin(0x1c, (a, b) => a << (b & 31));
  bin(0x1d, (a, b) => a >> (b & 31));
  bin(0x1e, (a, b) => (a >>> (b & 31)) | 0);
  bin(0x20, (a, b) => (a === b ? 1 : 0));
  bin(0x21, (a, b) => (a < b ? 1 : 0));
  bin(0x22, (a, b) => ((a >>> 0) < (b >>> 0) ? 1 : 0));
  H[0x00] = () => 0; // HALT
  H[0x01] = (next) => push((at(next, 1) << 24) >> 24); // PUSH8, sign-extended
  H[0x02] = (next) => push(at(next, 4) | (at(next, 3) << 8) | (at(next, 2) << 16) | (at(next, 1) << 24)); // PUSH32
  H[0x03] = () => { const bad = need(1); if (bad !== undefined) return bad; sp--; }; // POP
  H[0x04] = () => { const bad = need(1); if (bad !== undefined) return bad; return push(stack[sp - 1]); }; // DUP
  H[0x05] = () => { const bad = need(2); if (bad !== undefined) return bad; const t = stack[sp - 1]; stack[sp - 1] = stack[sp - 2]; stack[sp - 2] = t; }; // SWAP
  H[0x06] = () => { const bad = need(2); if (bad !== undefined) return bad; return push(stack[sp - 2]); }; // OVER
  H[0x07] = () => { const bad = need(3); if (bad !== undefined) return bad; const a = stack[sp - 3]; stack[sp - 3] = stack[sp - 2]; stack[sp - 2] = stack[sp - 1]; stack[sp - 1] = a; }; // ROT ( a b c -- b c a )
  H[0x17] = () => { const bad = need(1); if (bad !== undefined) return bad; stack[sp - 1] = (-(stack[sp - 1] | 0)) | 0; }; // NEG
  H[0x1b] = () => { const bad = need(1); if (bad !== undefined) return bad; stack[sp - 1] = ~(stack[sp - 1] | 0); }; // NOT
  H[0x30] = (next) => { pc = next + rel16(next); }; // JMP
  const jumpIf = (zero: boolean) => (next: number): Done => {
    const bad = need(1); if (bad !== undefined) return bad;
    if (((stack[--sp] | 0) === 0) === zero) pc = next + rel16(next);
  };
  H[0x31] = jumpIf(true); // JZ
  H[0x32] = jumpIf(false); // JNZ
  H[0x33] = (next) => { if (csp >= 64) return 7; rets[csp++] = next; pc = at(next, 2) | (at(next, 1) << 8); }; // CALL, unsigned absolute
  H[0x34] = () => { if (csp === 0) return 8; pc = rets[--csp]; }; // RET
  H[0x40] = () => { const bad = need(1); if (bad !== undefined) return bad; const a = stack[sp - 1] | 0; if (a < 0 || a > 255) return 6; stack[sp - 1] = mem[a]; }; // LOAD
  H[0x41] = () => { const bad = need(2); if (bad !== undefined) return bad; const a = stack[sp - 1] | 0; if (a < 0 || a > 255) return 6; const v = stack[sp - 2]; sp -= 2; mem[a] = v; }; // STORE ( v addr -- )
  H[0x50] = () => { const bad = need(1); if (bad !== undefined) return bad; const s = String(stack[sp - 1] | 0); if (olen + s.length > 65536) return 11; sp--; text += s; olen += s.length; }; // PRINT, all or nothing
  H[0x51] = () => { const bad = need(1); if (bad !== undefined) return bad; if (olen + 1 > 65536) return 11; text += String.fromCharCode((stack[--sp] | 0) & 255); olen++; }; // PUTC
  H[0x52] = () => push(cursor < inp.length ? inp[cursor++] : -1); // IN
  H[0x53] = () => { const bad = need(1); if (bad !== undefined) return bad; return (stack[--sp] | 0) & 255; }; // EXIT
  for (;;) {
    if (steps >= 1000000) return finish(10);
    if (pc < 0 || pc >= n) return finish(9);
    const op = prog[pc];
    const imm = op === 1 ? 1 : op === 2 ? 4 : op >= 0x30 && op <= 0x33 ? 2 : 0;
    const handler = H[op];
    if (handler === undefined) return finish(5);
    if (imm > 0 && pc + imm >= n) return finish(9);
    steps++;
    const next = pc + 1 + imm;
    pc = next;
    const code = handler(next);
    if (code !== undefined) return finish(code);
  }
}

for (const id of readdirSync(IN_DIR).sort()) {
  const r = runVM(new Uint8Array(readFileSync(join(IN_DIR, id, 'program.bin'))), new Uint8Array(readFileSync(join(IN_DIR, id, 'input.bin'))));
  mkdirSync(join(OUT_DIR, id), { recursive: true });
  writeFileSync(join(OUT_DIR, id, 'stdout.bin'), r.out);
  writeFileSync(join(OUT_DIR, id, 'exit.txt'), r.code + '\n');
}
