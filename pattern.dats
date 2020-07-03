#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"

staload "./pattern.sats"
staload "./string.sats"

implement pat_from_string(str) =
	let
		val h = str[0]
	in
		case+ h of
		| '?' when length(str) > 1 => (
			string_cut_head(str);
			pat_atom(str)
		)
		| '*' when length(str) > 1 => (
			string_cut_head(str);
			pat_mult(str)
		)
		| _ => pat_symbol(str)
	end

implement pat_print(p) =
	case+ p of
	| pat_symbol(s) => print(s)
	| pat_atom(s) => (print("?"); print(s))
	| pat_mult(s) => (print("*"); print(s))

implement pat_copy(p) =
	case+ p of
	| pat_symbol(s) => pat_symbol(gcopy(s))
	| pat_atom(s) => pat_atom(gcopy(s))
	| pat_mult(s) => pat_mult(gcopy(s))

implement pat_free(p) =
	case+ p of
	| ~pat_symbol(s) => gfree(s)
	| ~pat_atom(s) => gfree(s)
	| ~pat_mult(s) => gfree(s)


implement pattern_print(pat) =
	case+ pat of
	| list_vt_cons(p, ps) => (
		pat_print(p);
		print(" ");
		pattern_print(ps)
	)
	| list_vt_nil() => ()

implement pattern_copy(pat) =
	let
		implement list_vt_copylin$copy<Pat>(p) = pat_copy(p)
	in
		list_vt_copylin<Pat>(pat)
	end

implement pattern_free(pat) =
	let
		implement list_vt_freelin$clear<Pat>(p) = pat_free(p)
	in
		list_vt_freelin<Pat>(pat)
	end
