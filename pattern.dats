#define ATS_DYNLOADFLAG 0

staload "pattern.sats"
staload "prelude/DATS/list_vt.dats"

implement pat_print(p) =
	case+ p of
	| pat_symbol(s) => print(s)
	| pat_atom(s) => (print("?"); print(s))
	| pat_mult(s) => (print("*"); print(s))

implement pat_free(p) =
	case+ p of
	| ~pat_symbol(s) => strptr_free(s)
	| ~pat_atom(s) => strptr_free(s)
	| ~pat_mult(s) => strptr_free(s)


implement pattern_print(pat) =
	case+ pat of
	| list_vt_cons(p, ps) => (
		pat_print(p);
		print(" ");
		pattern_print(ps)
	)
	| list_vt_nil() => ()

implement pattern_free(pat) =
	let
		implement list_vt_freelin$clear<Pat>(p) = $effmask_all(pat_free(p))
	in
		list_vt_freelin<Pat>(pat)
	end
