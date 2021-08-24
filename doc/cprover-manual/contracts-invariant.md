# Invariant Clause

An _invariant_ clause specifies a property that must be preserved
by every iteration of a loop.
In general a loop has infinitely many invariants.
For instance, `true` is a trivial invariant that holds before the loop,
and after each iteration of the loop (thus, inductive).
However, it `true` is rarely useful --
it is an extremely imprecise abstraction of a loop,
which is generally not _sufficient_ to prove any subsequent assertions.

### Syntax

An _invariant_ clause accepts a valid Boolean expression
over the variables visible at the same scope as the loop.
Additionally, [history variables] are also allowed within invariant clauses.

```c
__CPROVER_loop_invariant(bool cond)
```

Invariant clauses may be specified just after the loop guard.
Multiple invariant clauses on the same loop are allowed,
and is equivalent to a single invariant clause that is a conjunction of those clauses.
A few examples are shown below.

```c
while(i < n)
__CPROVER_loop_invariant(0 <= i && i <= n)
{ ... }
```

```c
for(int i = 0; i < n; ++i)
__CPROVER_loop_invariant(0 <= i)
__CPROVER_loop_invariant(i <= n)
{ ... }
```

```c
do { ... }
while (i < n)
__CPROVER_loop_invariant(0 <= i)
__CPROVER_loop_invariant(i <= n);
```

**Important.** Invariant clauses must be free of _side effects_,
for example, mutation of local or global variables.


### Semantics

The loop invariant clause expands to several assumptions and assertions:
1. The invariant is asserted just before the first iteration
2. The invariant is assumed on a non-deterministic state to model a non-determistic iteration
3. The invariant is finally asserted again to establish its inductiveness

Mathematical induction is the working principle here.
(1) establishes the base case for induction, and
(2) & (3) establish the inductive case.
Therefore, the invariant must hold _after_ the loop execution for _any_ number of iterations.
The invariant, together with the negation of the loop guard,
must be sufficient to establish subsequent assertions.
If it is not, the abstraction is too imprecise and the user must supply a stronger invariant.

To illustrate the key idea,
consider the following [binary search] loop with invariant clauses:

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

The instrumented GOTO program is similar to the following high-level C program:

```c
#include <assert.h>

int binary_search(int val, int buf[], int size)
{
  if(size < 0) return -1;

  long lb = 0, ub = size - 1;
  long mid = (lb + ub) / 2;

  /* 1. assert invariant at loop entry */
  assert(0 <= lb && lb - 1 <= ub && ub < size);
  assert(mid == (lb + ub) / 2);

  /* 2. create a non-deterministic state for modified variables */
  havoc(lb, ub, mid);

  /* 3. establish invariant to model state at an arbitrary iteration */
  __CPROVER_assume(0 <= lb && lb - 1 <= ub && ub < size)
  __CPROVER_assume(mid == (lb + ub) / 2)

  /* 4. perform a single arbitrary iteration (or exit the loop) */
  if(lb <= ub)
  {
     if(buf[mid] == val) break;
     if(buf[mid] < val)
       lb = mid + 1;
     else
       ub = mid - 1;
     mid = (lb + ub) / 2;

    /* 5. assert the invariant to establish inductiveness */
    assert(0 <= lb && lb - 1 <= ub && ub < size);
    assert(mid == (lb + ub) / 2);

    /* 6. terminate this symbolic execution path; similar to "exit" */
    __CPROVER_assume(false);
  }

  assert(lb > ub || (0 <= mid && mid < size));
  return lb > ub ? -1 : mid;
}
```

[history variables]: contracts-history-variables.md

[binary search algorithm]: https://en.wikipedia.org/wiki/Binary_search_algorithm
