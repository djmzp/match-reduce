viewtypedef expression(n: int) = list_vt(Strptr1, n)
viewtypedef Expression = [n: nat] expression(n)

fn expression_new(): expression(0)
fn expression_copy(!Expression): Expression
fn expression_equal(!Expression, !Expression): bool
fn expression_print(!Expression): void
fn expression_free(Expression): void

overload = with expression_equal
overload gprint with expression_print
