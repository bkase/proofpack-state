// host/gpu.c -- does a `!` call actually reach the GPU in this process?
//
// `io_gpu` is the runtime's own answer: it is set once at start-up by
// `corpus_setup`, from whether a GPU was found and whether `--gpu off` was
// passed. Reading it is the only honest way to report an *actual* backend
// rather than a requested one, and SPEC 7.6 requires forced Metal mode to
// fail when GPU execution cannot occur rather than fall back silently.
//
// Like host/run_bytes.c this depends on the runtime's internals, which carry
// no ABI promise. Rebuild on every toolchain bump.

Term host_gpu_enabled_run(Env e, Term* f, IoWork* w) {
  return term_pak(io_gpu ? CID(True) : CID(False), 0);
}

static void __attribute__((constructor)) host_gpu_enabled_use(void) {
  io_eff(CID(Host.gpu_enabled), host_gpu_enabled_run, 0);
}
