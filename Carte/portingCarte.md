# Status of the Program Logics a la Carte port

This file describes the state of the Program Logics a la Carte port relative to the Rocq implementation. The original implementation is here: <https://gitlab.mpi-sws.org/iris/itree-program-logic/-/tree/master?ref_type=heads>

Not everything should be ported to Lean. In particular, the following parts should **not** be ported:

- The trace-based adequacy
- The executable interpreters (this is subsumed by the interpreters given by the coinductive library)
- The itree semantics for HeapLang (these are already provided by the coinductive library)
- The correspondence proof of the operational semantics for HeapLang
- The `islaris` folder
- The `ITreeToTranslate` infrastructure might not be necessary to port
- The `AnswerEqDecision` infrastructure might not be necessary to port
- eutt should be replaced by normal equality (and proofs simplified accordingly)

The `islaris` folder should not be ported, all filenames below are relative to the `src` folder.

## `src`

- [x] `angelic_choice.v`
  - `angelicE`: part of itree library
  - [x] `angelicH`
  - [x] wpi rules
  - `angelicEH`: part of itree library
  - [x] exec adequacy
- `axioms.v`: not necessary in Lean
- [x] `choice.v`
  - `demonicE`: part of the itree library
  - [x] `demonicH`
  - [x] wpi rules
  - `demonic_irel`: part of trace based adequacy, should not be ported
  - `demonic_ifn`: part of trace based adequacy, should not be ported
  - `demonicEH`: should be given by the itree library
  - [x] exec adequacy
- [ ] `exec.v` (split into `Core/Exec.lean`, `Core/HandlerAdequate.lean`, and `Core/Wpi_exec.lean`)
  - [x] `bi_close`
  - [x] `bi_mono0`
  - [ ] `lfp_tp`
  - `eHandler`, `seHandler`, `inEH`, `exec`: provided by the itree library
  - [ ] `(s)eHandlerAdequate` (in `Core/HandlerAdequate.lean`)
  - [ ] `wpi_tp` (in `Core/Wpi_exec.lean`)
  - [ ] `wpi_adequate` and `wpi_adequate_pure` (both in `Core/HandlerAdequate.lean`, the later has not been defined)
  - `sumEH`: part of itree library
  - `exec`-tactics: port if necessary
- [x] `halt.v`
  - `haltE`: part of the itree library
  - [x] `haltH`
  - [x] wpi rules
  - `halt_ifn` and corresponding adequacy: part of trace based adequacy, should not be ported
  - `haltEH`: part of itree library
  - [x] exec adequacy
- [x] `handler.v`
  - [x] `iHandler`
  - [x] `sumH`
  - [x] `inH`
  - [x] `wandH` (unclear if necessary)
  - [x] `Sequential`
- [ ] `heap.v`
  - `store`, ... functions part of itree library
  - [ ] `heapGS` and pointsto
  - [ ] wpi rules
  - `heap_irel`, `heap_ifn` and corresponding adequacy: part of trace based adequacy, should not be ported
- `interpreter.v`: should not be ported at the moment
- `itree.v`: necessary functionality from this file should be provided by the itree library
- [ ] `state.v`
  - `stateE`: part of itree library
  - [x] `stateH`
  - [ ] wpi rules (sorry for `wpi_set_state`)
  - `state_irel`, `state_ifn`, `interp_tr_state` and corresponding adequacy: part of trace based adequacy, should not be ported
  - `stateEH`: part of the itree library
  - [ ] exec adequacy
- [ ] `step.v`
  - `stepE`: part of the itree library
  - it is a bit unclear what to do with the rest of this file, should be discussed
- `trace.v`: not ported
- [ ] `ub.v`
  - `ubE`: part of the itree library (called `failE`)
  - [x] `ubH`
  - [ ] wpi rules (`wpi_fail` sorry)
  - `ub_ifn`, `interp_tr_ub` and corresponding adequacy: part of trace based adequacy, should not be ported
  - `ubEH`: part of the itree library
  - [x] exec adequacy
- [x] `void.v`
  - `voidE`: should be given by the itree library
  - the rest of the file is not necessary to port
- [ ] `wpi.v`
  - [x] `wpi` (split into `Core/Wpi.lean` and `WpiMask.lean`)
  - [x] Lemmas about `wpi` (eqit can become =)
  - [x] `wpi_mask`
  - [x] Lemmas and Notation about `wpi_mask` (eqit can become =)
    - [ ] invariant related (need `inv` and `iinv`)
    - [x] others
  - [x] `wpi_translation`: might be nice to have but unclear if necessary
  - [x] `inH`
  - tactics: unclear if necessary

## `src/threadpool`

- `ctrace.v`: part of trace based adequacy, should not be ported
- [ ] `exec.v`:
  - `threadpoolEH`: part of itree library (`concEH`)
  - [ ] exec adequacy
- [ ] `handler.v`:
  - `threadpoolE`: part of itree library (`concE`)
  - [ ] `threadpoolH`
  - [ ] wpi rules
- `scheduler.v`: part of trace based adequacy, should not be ported
- `interleaving.v`: part of trace based adequacy, should not be ported

## `src/heaplang`

TODO

## `src/examplelang`

TODO
