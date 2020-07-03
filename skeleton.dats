#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"

staload "./skeleton.sats"
staload "./string.sats"

implement ske_from_string(str) =
	let
		val h = str[0]
	in
		case+ h of
		| ':' when length(str) > 1 => (
			string_cut_head(str);
			ske_hole(str)
		)
		| _ => ske_symbol(str)
	end

implement ske_print(s) =
	case+ s of
	| ske_symbol(s) => print(s)
	| ske_hole(s) => (print(":"); print(s))

implement ske_copy(s) =
	case+ s of
	| ske_symbol(s) => ske_symbol(gcopy(s))
	| ske_hole(s) => ske_hole(gcopy(s))

implement ske_free(s) =
	case+ s of
	| ~ske_symbol(s) => strnptr_free(s)
	| ~ske_hole(s) => strnptr_free(s)


implement skeleton_print(ske) =
	case+ ske of
	| list_vt_cons(s, ss) => (
		ske_print(s);
		print(" ");
		skeleton_print(ss)
	)
	| list_vt_nil() => ()

implement skeleton_copy(ske) =
	let
		implement list_vt_copylin$copy<Ske>(s) = ske_copy(s)
	in
		list_vt_copylin<Ske>(ske)
	end

implement skeleton_free(ske) =
	let
		implement list_vt_freelin$clear<Ske>(s) = ske_free(s)
	in
		list_vt_freelin<Ske>(ske)
	end
