# Direct+StackAware merge notes

## Changes to CKLR

Added the following requirements for match_mem of inj and injp:

- meminj_global f: requires that if a global block is mapped, then it is mapped
  to itself (not to something else).
- match_astack a1 a2: requires the abstract stacks be nonempty, and the total
  stack size (the sum of sizes of all frames in all stages) of the target
  program is not larger than the source program, so that if the target program
  overflows the stack, it must be the fault of the source program, not the
  compiler.

Added the following requirements to the accessibility relation of inj and injp:

- `incr_without_glob j j'`: the difference between j and j' must be stack
  blocks. Formally speaking, if j b = None and j' b = Some (b', _), then
  b and b' are stack blocks, not global blocks. There are no distinctions
  between stack and global blocks.

## Changes to RTL semantics

Pushes a new stage on module boundary (i.e., initial state); the stage is
popped at final state. (Abstract stacks are, well, abstract, so that does not
matter to the “real” semantics of the program.) This is a solution to the
following problem:

Consider two functions f and g:

```
f := call g; return
g := return
```

After tail call recognition, it becomes

```
f := tail g; (return)
g := return
```

If the initial state already contain a frame in the first stage, e.g., the
external function foo tailcalls f(), the source stack would be
(left is callee, right is caller)

```
+---------+  +---------------+  +---------+
| Stage 1 |  | Stage 2       |  | Stage 3 |
| +-----+ |  | +---+ +-----+ |  | +-----+ |
| |  g  | |  | | f | | foo | |  | | bar | |
| +-----+ |  | +---+ +-----+ |  | +-----+ |
+---------+  +---------------+  +---------+
                    ^
                    |
                    +-- module boundary
```

After g and f returns, stages 2 and 3 remains. (A stage is popped
*after* executing Ireturn by the calling module, so stage 2 remains.)

The shape of the stack of the transformed program becomes

```
+---------------------+  +---------+
| Stage 1             |  | Stage 2 |
| +---+ +---+ +-----+ |  | +-----+ |
| | g | | f | | foo | |  | | bar | |
| +---+ +---+ +-----+ |  | +-----+ |
+---------------------+  +---------+
             ^
             |
             +-- module boundary
```

Both stages remains. the stack size of the source program is f + foo, but that
of the target program is g + f + foo, which is larger than the source program!
Making sure that the first stage is clear at module boundary solves this
problem.

Our first solution is to clear the last stage of astack when executing Ireturn.
This is correct as the only possible step from a Returnstate is a return step,
which pops the last stage of astack. (This allows the memory requirements
(match_mem) of query and reply be the same, which is a requirement of the CKLR
framework.) This solution does not work.

## Changes to Inliningproof

Modified inline_sizes to accomodate open modules. The modification is trivial.

<details>
<summary>
Before the change of the RTL semantics, we used a hack (which is NOT used now)
</summary>

The intuition of inline_sizes (before the merge) is depicted as below.
Left is callee, right is caller; top is source, bottom is target.

```
+-----------+  +-----------+  +-----------+  +-----------+
| Stage 1   |  | Stage 2   |  | Stage 3   |  | Stage 4   |
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |
| | frame | |  | | frame | |  | | frame | |  | | frame | |
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |
+-----------+  +-----------+  +-----------+  +-----------+
   \           |           |     \           |           |
      \                    |        \                    |
         \     |    V|     |           \     |    V|     |
            \              |              \              |
               \           |                 \           |
               +-----------+                 +-----------+
               | Stage 1'  |                 | Stage 2'  |
               | +-------+ |                 | +-------+ |
               | | frame | |                 | | frame | |
               | +-------+ |                 | +-------+ |
               +-----------+                 +-----------+
```

In the picture above, stages 1 and 2 are inlined into one stage 1'.
We require that the total size of stage 2 to be geq stage 1'.
In open semantics, the case would change:

```
                                             |---> stages provided by query
+-----------+  +-----------+  +-----------+  +-----------+  +-----------+
| Stage 1   |  | Stage 2   |  | Stage 3   |  | Stage 4   |  | Stage 5   |
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |
| | frame | |  | | frame | |  | | frame | |  | | frame | |  | | frame | |  .......
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |
+-----------+  +-----------+  +-----------+  +-----------+  +-----------+
  \            |           |    \            |
     \                     |       \
        \      |    V|     |          \      |             V|
           \               |             \
              \            |                \
               +-----------+                 +-----------+  +-----------+
               | Stage 1'  |                 | Stage 2'  |  | Stage 3'  |
               | +-------+ |                 | +-------+ |  | +-------+ |
               | | frame | |                 | | frame | |  | | frame | |  .......
               | +-------+ |                 | +-------+ |  | +-------+ |
               +-----------+                 +-----------+  +-----------+
```

There is no longer stage 4 >= stage 2'; we need to treat the first set
of inlined stages differently from the rest of the stages.

</details>

## Changes to Tailcallproof

Modified tc_sizes to accomodate open modules. The modification is trivial.

<details>
<summary>
Before the change of the RTL semantics, we used a hack (which is NOT used now):
</summary>

The intuition of tc_sizes (before the merge) is depicted as below.
Left is callee, right is caller; top is source, bottom is target.

```
+-----------+  +-----------+  +-----------+  +-----------+
| Stage 1   |  | Stage 2   |  | Stage 3   |  | Stage 4   |
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |
| | frame | |  | | frame | |  | | frame | |  | | frame | |
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ |
+-----------+  +-----------+  +-----------+  +-----------+
|                          |  |                          |
|            =             |  |             =            |
|                          |  |                          |
+--------------------------+  +--------------------------+
| Stage 1'                 |  | Stage 2'                 |
| +-------+      +-------+ |  | +-------+      +-------+ |
| | frame |      | frame | |  | | frame |      | frame | |
| +-------+      +-------+ |  | +-------+      +-------+ |
+--------------------------+  +--------------------------+
```

The stages are merged together for tail calls. In open semantics:

```
                                                         |---> frames provided by query
+-----------+  +-----------+  +-----------+  +---------------------+  +-----------+
| Stage 1   |  | Stage 2   |  | Stage 3   |  | Stage 4             |  | Stage 5   |
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ +-------+ |  | +-------+ |
| | frame | |  | | frame | |  | | frame | |  | | frame | | frame | |  | | frame | |  .......
| +-------+ |  | +-------+ |  | +-------+ |  | +-------+ +-------+ |  | +-------+ |
+-----------+  +-----------+  +-----------+  +---------------------+  +-----------+
|                          |  |                         |
|            =             |  |             =           |            V|
|                          |  |                         |
+--------------------------+  +------------------------------------+  +-----------+
| Stage 1'                 |  | Stage 2'                |          |  | Stage 3'  |
| +-------+      +-------+ |  | +-------+      +-------+ +-------+ |  | +-------+ |
| | frame |      | frame | |  | | frame |      | frame | | frame | |  | | frame | |  .......
| +-------+      +-------+ |  | +-------+      +-------+ +-------+ |  | +-------+ |
+--------------------------+  +------------------------------------+  +-----------+
```

</details>
