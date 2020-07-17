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
		| '=' when length(str) > 1 => (
			string_cut_head(str);
			pat_bal(str)
		)
		| '_' when length(str) = 1 => (
			gfree(str);
			pat_under
		)
		| '.' when length(str) = 3 =>
			if str[1] = '.' && str[2] = '.' then (
				gfree(str);
				pat_ellip
			) else (
				pat_symbol(str)
			)
		| _ => pat_symbol(str)
	end

implement pat_print(p) =
	case+ p of
	| pat_symbol(s) => print(s)
	| pat_atom(s) => (print("?"); print(s))
	| pat_mult(s) => (print("*"); print(s))
	| pat_bal(s) => (print("="); print(s))
	| pat_under() => print("_")
	| pat_ellip() => print("...")

implement pat_copy(p) =
	case+ p of
	| pat_symbol(s) => pat_symbol(gcopy(s))
	| pat_atom(s) => pat_atom(gcopy(s))
	| pat_mult(s) => pat_mult(gcopy(s))
	| pat_bal(s) => pat_bal(gcopy(s))
	| pat_under() => pat_under()
	| pat_ellip() => pat_ellip()

implement pat_free(p) =
	case+ p of
	| ~pat_symbol(s) => gfree(s)
	| ~pat_atom(s) => gfree(s)
	| ~pat_mult(s) => gfree(s)
	| ~pat_bal(s) => gfree(s)
	| ~pat_under() => ()
	| ~pat_ellip() => ()

implement pat_free'(p) =
	case+ p of
	| ~pat_symbol(s) => gfree(s)
	| ~pat_atom(s) => gfree(s)
	| ~pat_mult(s) => gfree(s)
	| ~pat_bal(s) => gfree(s)
	| ~pat_under() => ()
	| ~pat_ellip() => ()

implement pattern_length(pat) =
	let
		fun loop {n: nat} (pat: !Pattern, acc: int(n)): [m: nat | m >= n] int(m) =
			case+ pat of
			| list_vt_cons(pat_mult(_), ps) => loop(ps, acc)
			| list_vt_cons(pat_ellip(), ps) => loop(ps, acc)
			| list_vt_cons(_, ps) => loop(ps, acc + 1)
			| list_vt_nil() => acc
	in
		loop(pat, 0)
	end

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
