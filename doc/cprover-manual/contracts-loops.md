# Loop Contracts

CBMC offers support for loop contracts, which includes three basic clauses:
- _invariant_ clause for establishing safety properties
- _decreases_ clause for establishing termination, and
- _assigns_ clause for declaring the subset of variables that is modifiable in the loop.

These clauses formally describe an abstraction of a loop for the purpose of a proof.
CBMC also provides a series of built-in constructs
to aid writing loop contracts (e.g., _history variables_ and _quantifiers_).

## Overview

Consider an implementation of the [binary search algorithm] below.

```c
#include <assert.h>

int binary_search(int val, int buf[], int size)
{
  if(size < 0) return -1;

  long lb = 0, ub = size - 1;
  long mid = (lb + ub) / 2;

  while(lb <= ub)
  {
     if(buf[mid] == val) break;
     if(buf[mid] < val)
       lb = mid + 1;
     else
       ub = mid - 1;
     mid = (lb + ub) / 2;
  }
  assert(lb > ub || (0 <= mid && mid < size));
  return lb > ub ? -1 : mid;
}
```

The function stores a lower bound `lb` and an upper bound `ub`
initialized to the bounds on the buffer `buf`, i.e., to `0` and `size-1` respectively.
In each iteration, the midpoint `mid` is compared against the target value `val`
and in case of a mismatch either the lower half or the upper half of the buffer is searched recursively.
A developer might be interested in verifying two high-level properties on the loop on all possible buffers `buf` and values `val`:
1. an out-of-bound access should never occur (at `buf[mid]` lookup)
2. the loop must eventually always terminate

To prove the first (memory-safety) property,
we may declare _loop invariants_ that must be preserved across all loop iterations.
In this case, two invariant clauses would together imply that `buf[mid]` lookup is always safe.
The first invariant clause would establish that the bounds (`lb` and `ub`) are always valid:
```c
__CPROVER_loop_invariant(0 <= lb && lb - 1 <= ub && ub < size)
```
Note that in the second conjunct, `lb - 1 == ub` case is possible when the value `val` is not found in the buffer `buf`.
The second invariant clause would establish that the midpoint `mid` is always a valid index.
In this particular case we can in fact establish a stronger invariant,
that `mid` is indeed always the midpoint of `lb` and `ub` in every iteration:
```c
__CPROVER_loop_invariant(mid == (lb + ub) / 2)
```

To prove the second (termination) property,
we may declare a _decreases clause_ that indicates a bounded numeric measure which must monotonically decrease with each loop iteration.
In this case, it is easy to see that `lb` and `ub` are approaching closer together with each iteration, since either `lb` must increase or `ub` must decrease in each iteration.
```c
__CPROVER_decreases(ub - lb)
```

The loop together with all its contracts is shown below.

```c
#include <assert.h>

int binary_search(int val, int buf[], int size)
{
  if(size < 0) return -1;

  long lb = 0, ub = size - 1;
  long mid = (lb + ub) / 2;

  while(lb <= ub)
  __CPROVER_loop_invariant(0 <= lb && lb - 1 <= ub && ub < size)
  __CPROVER_loop_invariant(mid == (lb + ub) / 2)
  __CPROVER_decreases(ub - lb)
  {
     if(buf[mid] == val) break;
     if(buf[mid] < val)
       lb = mid + 1;
     else
       ub = mid - 1;
     mid = (lb + ub) / 2;
  }
  assert(lb > ub || (0 <= mid && mid < size));
  return lb > ub ? -1 : mid;
}
```

With CBMC we can now generate an unbounded proof using these contracts:

```sh
# compile the C program to a GOTO binary
goto-cc -o binary_search.goto binary_search.c

# instrument loops using specified loop contracts
goto-instrument --apply-loop-contracts binary_search.goto binary_search.2.goto

# run CBMC to check the instrumented program
cbmc binary_search.2.goto --signed-overflow-check --function binary_search
```

## Additional Resources

- [Assigns Clause](contracts-assigns.md)
- [Decreases Clause](contracts-decreases.md)
- [History Variables](contracts-history-variables.md)
- [Invariant Clause](contracts-invariant.md)
- [Quantifiers](contracts-quantifiers.md)

[binary search algorithm]: https://en.wikipedia.org/wiki/Binary_search_algorithm
