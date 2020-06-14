#define ATS_DYNLOADFLAG 0

staload "skeleton.sats"
staload "prelude/DATS/list_vt.dats"

implement ske_print(s) =
	case+ s of
	| ske_symbol(s) => print(s)
	| ske_hole(s) => (print(":"); print(s))

implement ske_free(s) =
	case+ s of
	| ~ske_symbol(s) => strptr_free(s)
	| ~ske_hole(s) => strptr_free(s)


implement skeleton_print(ske) =
	case+ ske of
	| list_vt_cons(s, ss) => (
		ske_print(s);
		print(" ");
		skeleton_print(ss)
	)
	| list_vt_nil() => ()

implement skeleton_free(ske) =
	let
		implement list_vt_freelin$clear<Ske>(s) = ske_free(s)
	in
		list_vt_freelin<Ske>(ske)
	end
