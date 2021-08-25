# Decreases Clause

We use decreases clauses to prove termination of loops.
Given a loop, its decrease clause is a function `f` from program states to values such that
- the codomain of `f` is bounded below;
- `f` strictly decreases in all iterations of the loop.

Because the codomain is bounded below, `f` cannot strictly decrease forever. 
This means the loop cannot run forever.
Therefore, it must eventually terminate.

In the scientific literature, decreases clauses are commonly known as loop variants or ranking functions.

### Syntax

A one-dimensional decreases clause is an expression over the variables visible at the same scope as the loop.
The type of the one-dimensional decreases clause must be an arithmetic type (e.g. int and double).
Unlike mathematical integers, arithmetic types in C are all bounded below.
Furthermore, unlike mathematical real numbers, floating-point arithmetic types in C are not dense.
Hence, it is impossible for an arithmetic-typed function in C to strictly decrease forever.  

We use the syntax `__CPROVER_decreases(f)` to specify a decreases clause.
It must be placed between a loop guard and the loop body. 
Also, if the loop also has invariant clauses, then the decreases clause must be placed after these invariant clauses and before the loop body.

An example of a one-dimensional decreases clause is shown below.

```c
while(i < n)
__CPROVER_loop_invariant(0 <= i && i <= n)
__CPROVER_decreases(n - i)
{ ... }
```

CBMC supports not only one-dimensional decreases clauses but also multi-dimensional ones.
A multi-dimensional decreases clause is a vector of arithmetic-typed expressions
To compare two vectors for strong inequality, we use lexicographic order.
We use the syntax `__CPROVER_decreases(f_1, f_2, ..., f_n)`.
An example of a multi-dimensional decreases clause is given below.

```c
while(i < n)
__CPROVER_loop_invariant(0 <= i && i <= n && 0 <= j && j <= n)
__CPROVER_decreases(n - i, n - j)
{
  if (j < n)
    j++;
  else
  {
    i++;
    j = 0;
  }
}
```

**Important.** Decreases clauses must be free of side effects.

### Semantics

Suppose we want to verify a (possibly multidimensional) decreases clause `f`.

As described in [here](contracts-invariant.md), during the instrumentation for a loop contract, CBMC replaces a loop by its single iteration; that is, the back edge of the loop is removed. 
CBMC then inserts additional assumptions and assertions to the resulting code in order to prove the base case and inductive case of a loop invariant (if exists).
If a loop invariant is missing (but a decreases clause is present), then CBMC uses a trivial loop invariant of `true` for instrumentation.

After having replaced the loop with its single iteration, to verify the decreases clause `f`, CBMC inserts the following instructions to the code:
1. Declare two temporary variables;
2. Assign `f` to the first temporary variable at the beginning of the loop body;
3. Assign `f` to the second temporary variable at the end of the loop body;
4. Assert that the second temporary variable is strictly smaller than the first one;
5. Remove the two temporary variables after the loop.

If `f` is a one-dimensional decreases clause, the step (4) will use the standard arithmetic inequality (i.e. `<`).
If `f` is a multi-dimensional decreases clause, step (4) uses lexicographic order to compare two vectors.
Formally, given two vectors `(a_1, ... a_n)` and `(b_1, ..., b_n)` of the same size, their lexicographic order (denoted by `(a_1, ... a_n) < (b_1, ..., b_n)`) is defined as 
```
a_1 < b_1 || (a_1 == b_1 && a_2 < b_2) || ... || (a_1 == b_1 && ... && a_{n-1} == b_{n-1} && a_n < b_n),
```
where `||` is disjunction and `&&` is conjunction.

By way of example, consider the following C code:
```c
int i = 0;
int n = ...;

while(i < n)
__CPROVER_loop_invariant(0 <= i && i <= n)
__CPROVER_decreases(n - i)
{
  i++;
}
```

After instrumentation, we will obtain GOTO code that is semantically equivalent to the following C code:
```c
int i = 0;
int n = ...;

/* 1. assert invariant at loop entry */
assert(0 <= i && i <= n)

/* 2. create a non-deterministic state for modified variables */
havoc(i);

/* 3. establish invariant to model state at an arbitrary iteration */
__CPROVER_assume(0 <= i && i <= n);

/* 4. perform a single arbitrary iteration (or exit the loop) */
if(i < n)
{
  /* 5. declare two temporary variables for storing the decreases clause's values */
  int temp1;
  int temp2;

  /* 6. Evaluate the decreases at the start of the loop body */
  temp1 = n - i;

  i++;

  /* 7. Evaluate the decreases at the start of the loop body */
  temp2 = n - i;

  /* 8. assert the invariant to establish inductiveness */
  assert(0 <= i && i <= n);

  /* 9. assert that the decreases clause indeed strictly decreases after one arbitrary loop iteration */
  assert(temp2 < temp1);

  /* 10. terminate this symbolic execution path; similar to "exit" */
  __CPROVER_assume(false);
}
```

**Important.** 
Keep in mind that decreases clauses work in conjunction with loop invariants.
Conceptually, a loop invariant characterizes the (super)set of all reachable states in a loop.
If we do not annotate a loop with a loop invariant but only with a decreases clause, the decreases clause must be valid (i.e. bounded below and strictly decreasing) over the "whole" state space, including those states that are in fact unreachable in the loop.
Providing such a loop invariant that works for the whole state space can be difficult (or possibly even impossible). 
Hence, to prove termination of a loop, it is critical to provide a sufficiently precise loop invariant as well as a valid decreases clause.

**Warning.** 
In some cases, the current implementation does not place the assignment of a decreases clause to the first temporary variable in the right location of the GOTO code. 
This happens when a C loop guard is translated to a multi-line GOTO loop guard. 
High-level C code is compiled to low-level GOTO code before instrumentation. 
Hence, in the instrumentation phase, we no longer have access to the original C code.
Furthermore, it is non-trivial to clearly tell the borderline between a loop guard and a loop body in the GOTO code. 
Consequently, if the GOTO loop guard consists of multiple instructions, the first assignment of the decreases clause will be inserted in the middle of the multi-line GOTO loop guard. 
