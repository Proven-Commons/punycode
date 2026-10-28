// The Node oracle for tests/run_tests.py: punycode.js as Node bundles
// it (require('punycode')), driven line by line.
//
//   e HEX   encode the text whose UTF-8 bytes the hex digits give
//   d HEX   decode the Punycode string whose UTF-8 bytes they give
//
// Each answer is "OK " and the output (the Punycode string as hex of
// its UTF-8 bytes, or the code points as hex joined by ","), or "ERR "
// and the message punycode.js threw.
'use strict';
process.noDeprecation = true;
const punycode = require('punycode');
const readline = require('readline');

function fromHex(h) {
  return Buffer.from(h, 'hex').toString('utf8');
}

const out = [];
const rl = readline.createInterface({ input: process.stdin, crlfDelay: Infinity });
rl.on('line', (line) => {
  const sp = line.indexOf(' ');
  const op = sp < 0 ? line : line.slice(0, sp);
  const arg = sp < 0 ? '' : line.slice(sp + 1);
  try {
    if (op === 'e') {
      out.push('OK ' + Buffer.from(punycode.encode(fromHex(arg)), 'utf8').toString('hex'));
    } else if (op === 'd') {
      const s = punycode.decode(fromHex(arg));
      out.push('OK ' + Array.from(s, (c) => c.codePointAt(0).toString(16)).join(','));
    } else {
      out.push('error');
    }
  } catch (e) {
    out.push('ERR ' + String(e && e.message).replace(/\s+/g, '_'));
  }
  if (out.length >= 1024) { process.stdout.write(out.join('\n') + '\n'); out.length = 0; }
});
rl.on('close', () => {
  if (out.length) process.stdout.write(out.join('\n') + '\n');
  process.stdout.write('');
});
