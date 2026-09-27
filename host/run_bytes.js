// host/run_bytes.js -- the JavaScript twin of host/run_bytes.c.
//
// Serves `bend pp.bend` (the interpreter) and `bend pp.bend -o pp.js`; the .c
// serves a native build. Same contract: literal argv, no shell, stdout as
// bytes, stderr as text.

function host_run_bytes(program, args, input, maxOutput, timeoutMs) {
  const argv = [program];
  for (let xs = args; xs.$ === CID(Con); xs = xs.tail) {
    argv.push(xs.head);
  }
  if (maxOutput === 0 || timeoutMs === 0
    || argv.some((arg) => arg.includes("\0"))) {
    return io_fail(22);
  }
  let got;
  try {
    got = Bun.spawnSync({ cmd: argv, stdin: Buffer.from(input),
      stdout: "pipe", stderr: "pipe", timeout: timeoutMs,
      maxBuffer: maxOutput + 1 });
  } catch (e) {
    return io_fail(typeof e.errno === "number" ? Math.abs(e.errno) : 5);
  }
  const out = Buffer.from(got.stdout ?? []);
  const err = Buffer.from(got.stderr ?? []);
  if (got.exitedDueToMaxBuffer || out.length + err.length > maxOutput) {
    return io_fail(27);
  }
  if (got.exitedDueToTimeout) {
    return io_fail(process.platform === "darwin" ? 60 : 110);
  }
  const sig = got.signalCode === null ? 0
    : require("node:os").constants.signals[got.signalCode];
  const code = got.exitCode ?? (128 + (sig ?? 0));
  // Bytes, not text: the same reason the .c gives.
  let xs = { $: CID(Nil) };
  for (let i = out.length; i > 0; i -= 1) {
    xs = { $: CID(Con), head: out[i - 1], tail: xs };
  }
  return io_done(io_tup(code, xs, err.toString("utf8")));
}

io_eff(CID(Host.run_bytes), host_run_bytes);
