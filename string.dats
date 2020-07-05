#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"

staload "./string.sats"

implement string_new(s) =
	let
		val res = string1_copy(s)
		val () = assertloc(strnptr_isnot_null(res))
	in
		res
	end

implement string_copy(str) =
	let
		val s = strnptr_copy(str)
		val () = assertloc(strnptr_isnot_null(s))
	in
		s
	end

implement string_compare(str1, str2) =
	let
		val s1 = strnptr2strptr(gcopy(str1))
		val s2 = strnptr2strptr(gcopy(str2))
		val res = compare_strptr_strptr(s1, s2)
	in
		strptr_free(s1);
		strptr_free(s2);
		res
	end

implement string_equal(str1, str2) = string_compare(str1, str2) = 0

implement string_print(str) = print_strnptr(str)

extern fun memmove(dst: ptr, src: ptr, size: ssize_t): void = "mac#"
/// XXX !!!!!!! THIS IS NOT SAFE !!!!!!!
// ATS thinks that the string is still the same size, but I just don't know
// how to tell it that the size is decreased when calling an external C function
implement string_cut_head(s) =
	memmove(strnptr2ptr(s), ptr_succ<char>(strnptr2ptr(s)), strnptr_length(s))

implement string_free(str) = strnptr_free(str)
