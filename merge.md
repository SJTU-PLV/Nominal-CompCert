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

## Changes to RTL semantics

(WIP, could be reverted) clears the last stage of astack when executing Ireturn.
This is correct as the only possible step from a Returnstate is a return step,
which pops the last stage of astack. This allows the memory requirements
(match_mem) of query and reply be the same, which is a requirement of the CKLR
framework.

## Changes to Inliningproof

Modified inline_sizes to accomodate open modules.

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

## Changes to Tailcallproof (WIP)

Modified tc_sizes to accomodate open modules.
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
