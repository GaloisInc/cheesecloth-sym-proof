Advice is recorded and refined in several stages, from the first stage which is
the secret handwritten proof to the last stage which is run online in ZK.

There are several parts of the original proof we wish to replace with advice:

1. The original proof executes proof steps in a hardcoded sequence; the ZK
   checker should instead choose steps based on advice, so that the proof
   itself remains secret.
2. The original proof uses high-level tactics; the ZK checker should call rules
   directly, which is simpler.  This also eliminates any searches or temporary
   `Term`/`Prop` construction that tactics might perform.
3. The original proof allocates terms as needed; the ZK checker should start
   with all terms preloaded in initial memory.
4. The original proof uses `HashMap` lookups for interning terms; the ZK
   checker should find the right term in the table by advice instead.
5. The original proof constructs terms to pass to proof rules; the ZK checker
   should instead pick a pre-constructed term from the interning table.
6. The original proof performs searches by linear scan; the ZK checker should
   get the search result as advice.
7. The original proof grows `Vec`s incrementally; the ZK checker should
   allocate each `Vec` with the proper length from the start, which avoids
   reallocation and copies.

## Stage 0

In this stage, we run the original proof (e.g. `src/bin/proof_grit.rs`) with
recording enabled.

In this stage, each time the proof calls a `rule_*` method (directly or through
a tactic), the rule and its arguments are recorded as advice.  The
serialization of arguments as advice effectively describes how to reconstruct
each `Prop`, `Term`, or other value that appears as a rule argument.

Slice searches performed during this stage as part of a proof rule will also
record the index where the target item was found.  We do this early because it
allows skipping construction of some terms.  In particular, when playing back
this advice, rules that use `require_premise_one_of` can construct only the
premise that was actually found, rather than constructing all candidate
premises.

This stage eliminates tactics and the hardcoded proof structure, handling
points (1) and (2).

* Reads: (none)
* Writes `rules`: rule invocations and some arguments.
* Writes `props`: serialized `Prop`s appearing in rule arguments.
* Writes `states`: serialized `symbolic::State`s appearing in rule arguments.
* Writes `terms`: serialized `Term`s appearing in rule arguments.
* Writes `search_index`: for each search operation, contains the index where
  the target value was found.

## Stage 1

In this stage, we replay the rule invocations (including reconstructing any
necessary `Term`s, `Prop`s, or other arguments) from advice, and record
additional, finer-grained advice.

The reason some advice is not recorded until this stage is to avoid including
unnecessary values in the advice stream.  For example, when recording `Term`s,
we want to include only `Term`s that are actually necessary for the proof and
ignore any `Term`s that might be constructed as temporaries in certain tactics.

In this stage, each time `Term::intern` allocates a new `Term`, it also records
the `TermKind` in a table of terms; these will be the preallocated terms used
in later stages.  Also, when a rule argument contains a `Term`, this stage
records the index of that term in the table, which can be used in place of the
serialized term.

Note that this stage does *not* record advice for `Term::intern`.  We need to
eliminate calls to `Term::intern` for rule arguments before recording that
advice, since the ZK checker calls `Term::intern` only for `Term`s constructed
internally by the proof kernel, and simply picks `Term`s from the table for
rule arguments.  However, all `Term`s, including rule arguments, must appear in
the final table.  So we have this stage build the table and also eliminate rule
argument `Term::intern` calls, and then have the next stage compute interning
advice for the remaining `Term::intern` calls.

This stage handles points (3) and (5).

* Reads: `rules`, `search_index`, `props`, `states`, `terms`
* Writes `term_table`: an array containing the `TermKind`s of all `Term`s used
  in the proof.  Note this is not an advice stream (a sequence of words), but
  rather a table that can be placed in initial memory.
* Writes `term_index`: contains an index into `term_table` for each `Term`
  appearing in rule arguments.  This replaces `terms`.

## Stage 2

Here we again replay rule invocations and record additional advice.

In this stage, `Term::intern` looks up terms in the preallocated `term_table`
constructed by the previous stage and records the index where it finds each
term for interning purposes.  Also, `AVec`s record their peak lengths.

This stage handles points (4), (6), and (7).

* Reads: `rules`, `search_index`, `props`, `states`, `term_table`, `term_index`
* Writes `term_intern_index`: contains an index into `term_table` where the
  result of each `Term::intern` call can be found.
* Writes `avec_len`: contains the maximum length of each `AVec` over its
  lifetime, so the proper capacity can be allocated up front.

## Stage 3

This is the final zero-knowledge proof checker, which can be compiled to run in
MicroRAM.  It reads the previously recorded advice and uses it to efficiently
check the proof.

* Reads: `rules`, `search_index`, `props`, `states`, `term_table`,
  `term_index`, `term_intern_index`, `avec_len`
