Advice is recorded and refined in several stages, from the first stage which is
the secret handwritten proof to the last stage which is run online in ZK.

We record advice in several indepedent streams.  Each stage of advice
generation reads some streams and generates others.  Splitting advice into
separate streams lets us read the same advice across several stages without
worrying about how it interleaves with newly generated advice from the later
stages.  It also helps with debugging, since a bug in generation of one advice
stream can't affect other streams.

Advice generation stages are defined as the various `stageN` features in
`Cargo.toml`.  See that file for details of which advice is recorded or played
back in each stage.

We currently define the following advice streams:

## `rules`

This is actually split into three streams, `rules`, `props`, and `states`, but
they are always recorded and played back together, controlled by the
`recording_rules` and `playback_rules` Cargo features.  Together, these
describe a transcript of all the `kernel::Proof` rules invoked during the proof
and the arguments that were passed to those rules.  The exception is that any
`Term` arguments, including `Term`s embedded in `Prop`s or states, are recorded
in either the `terms` or `term_index` stream, depending on which stage of
advice generation is running.

The serialized arguments in this stream are represented as a sequence of values
that essentially describes how to build the argument value from scratch.

Dependencies:

* Before `term_table`

The `rules` stream is recorded first, in stage 0, because it allows running the
proof without calling tactics, and thus eliminates unneeded temporary values
and failed attempts to apply rules (as in `try_rule_step`).  In particular,
this eliminates unneeded `Term`s so they won't be included in the `term_table`
advice.

## `terms`

This stream describes how to build each `Term` used in rule arguments through a
sequence of `Term` constructor applications.  It is recorded in conjunction
with `rules`, and is played back with `rules` until the `term_index` stream is
available to replace it.

## `search_index`

Certain proof rules involve searching data structures, such as checking whether
a particular `Prop` is present in the proof context.  For each search, this
stream records where the value was found; during playback, the proof checker
can simply check that the element at that location satisfies the query.

In some cases, a proof rule may search for any of N different forms of a value.
For those searches, this advice stream records which of the N variants was
actually found.  When playing back this advice, only the matching variant needs
to be constructed; the non-matching variants are omitted.

Dependencies:

* After `rules` (or at the same time as `rules`, as an optimization)

`search_index` should be recorded after `rules` so it doesn't record any
searches performed within tactics.  However, currently only proof rules record
into this stream, so as an optimization, we can record it at the same time as
`rules`.

## `term_table`

This "advice stream" is actually a table of preconstructed `Term` values, which
will be provided as secret initial memory in the ZK proof checker.  It includes
every `Term` that is used anywhere in the proof, so there is no need to
allocate terms at run time.

Dependencies:

* After `rules`
* After `search_index`

We'd like to make this table as small as possible, so any advice optimizations
that eliminate `Term`s from the proof should be done before this advice stream
is recorded.  Playing back `rules` eliminates any temporary `Term`s that might
be constructed in tactics.  Playing back `search_index` allows skipping
construction of non-matching values in one-of-N searches, which can eliminate
more temporary `Term`s.

## `term_index`

This stream represents terms used in rule arguments as indices into
`term_table`.  Once `term_index` has been recorded, it is used instead of
`terms` in later stages.  Playing back `term_index` is more efficient than
playing back `terms` because it only mentions the top-level term, whereas
`terms` describes every sub-term.

Dependencies:

* After or at the same time as `term_table`

Since the values in this stream are indices into `term_table`, `term_table`
must be constructed first.

## `term_intern_index`

This stream contains indices into the `term_table`, similar to `term_index`,
but these indices are used by `Term::intern` to locate the preallocated,
interned version of ecah term, rather than when building rule arguments.

Dependencies:

* After `term_table`
* After `term_index`

Playing back `term_index` advice causes terms in rule arguments to be looked up
from the `term_table` rather than constructed with `Term::intern` (or other
constructors that dispatch to `Term::intern`).  Since `term_intern_index`
contains advice for each `Term::intern` call, it must be recorded after this
optimization that eliminates `Term::intern` calls.

## `avec_len`

For each `AVec` constructed during proof checking, this stream contains the
maximum length that the `AVec` will grow to.  This allows allocating an
appropriate amount of memory up front and lets us avoid growing the vector
dynamically, which involves an expensive `memcpy` operation.

Dependencies:

* After `rules`

This stream identifies vectors by the order in which they are constructed,
which means eliminating (or adding) vectors afterward would invalidate the
recorded advice.  Any advice optimizations that may eliminate `AVec`s must run
before `avec_len` is recorded, so we require `rules` to be recorded first
(eliminating temporaries in tactics).

Note that `symbolic::State` may contain `AVec`s (depending on the choice of
memory representation).

## `amap_keys`

For each `AMap` constructed during proof checking, this stream contains the
set of all keys that will be inserted into the map (including keys that are
inserted but later removed).  This allows allocating the map up front as a flat
vector of `(Key, Option<Value>)` pairs and allows efficient lookups for both
present and absent keys; see the `AMap` doc comments for more details on the
implementation.

Dependencies:

* After `rules`

Like `avec_len`, this stream identifies maps by the order of construction, so
advice optimizations that eliminate maps must happen first.

## `amap_access`

For each lookup into an `AMap`, this stream contains an index used to
accelerate the lookup.  For successful lookups, this is the index of the entry
with a matching key.  See comments in `AMap::get_index` for details.

Dependencies:

* After `amap_keys`

Each value in the stream is an index into the entries of a map, and the number
and order of entries depends on the complete key set across the lifetime of the
map.  So those indices can't be computed until the full key set (as recorded in
`amap_keys`) is known.

## `linear`

Consists of all previous advice streams (except `term_table`) flattened into a
single linear sequence.  Different streams are interleaved as needed based on
the order in which they are used.  This stream is the final output of advice
generation and can be passed to the MicroRAM interpreter for use when building
the program trace.

Dependencies:

* After all other advice streams
