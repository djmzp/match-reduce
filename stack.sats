#include "share/atspre_staload.hats"

// Will possibly be used in the future

viewtypedef stack(a: viewt@ype, n: int) = list_vt(a, n)
viewtypedef Stack(a: viewt@ype) = [n: nat] stack(a, n)

fn {a: viewt@ype} stack_push {n: nat} (&stack(a, n) >> stack(a, n + 1), a): void
fn {a: viewt@ype} stack_pop {n: int | n > 0} (&stack(a, n) >> stack(a, n - 1)): a
fn {a: viewt@ype} stack_is_empty {n: nat} (!stack(a, n)): bool
