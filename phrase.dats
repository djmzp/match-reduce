#define ATS_DYNLOADFLAG 0

staload "./phrase.sats"
staload "./string.sats"

#include "share/atspre_staload.hats"

// I don't know what I'm missing here:
// staload "prelude/DATS/integer.dats"
// staload "prelude/DATS/string.dats"
// staload "prelude/DATS/strptr.dats"
// staload "prelude/DATS/list_vt.dats"

implement phrase_new() = list_vt_nil()

implement phrase_copy(ph) =
	let
		implement list_vt_copylin$copy<String>(s) = string_copy(s)
	in
		list_vt_copylin<String>(ph)
	end

implement phrase_equal(ph1, ph2) =
	case+ (ph1, ph2) of
	| (list_vt_nil(), list_vt_nil()) => true
	| (list_vt_cons(p1, ps1), list_vt_cons(p2, ps2)) =>
		if compare(p1, p2) = 0 then
			true && phrase_equal(ps1, ps2)
		else
			false
	| (_, _) => false

implement phrase_print(ph) =
	case+ ph of
	| list_vt_cons(p, ps) => (
		gprint(p);
		print(" ");
		phrase_print(ps)
	)
	| list_vt_nil() => ()

implement phrase_free(ph)=
	let
		implement list_vt_freelin$clear<String>(s) = gfree(s)
	in
		list_vt_freelin<String>(ph)
	end
