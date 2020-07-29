#define ATS_DYNLOADFLAG 0

staload "./stack.sats"

implement {a} stack_push(st, x) = st := list_vt_cons(x, st)

implement {a} stack_pop(st) = x where {
	val+ ~list_vt_cons(x, xs) = st
	val () = st := xs
}

implement {a} stack_is_empty(st) = length(st) = 0
