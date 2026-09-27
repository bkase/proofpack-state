// host/gpu.js -- the JavaScript twin of host/gpu.c.
//
// The JavaScript target ignores parallelism entirely and runs sequentially,
// so a `!` call never reaches a GPU there. Reporting `false` is the truth
// for this lane, not a stub.

function host_gpu_enabled() {
  return false;
}

io_eff(CID(Host.gpu_enabled), host_gpu_enabled);
