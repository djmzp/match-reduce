#define ATS_DYNLOADFLAG 0

#include "share/atspre_staload.hats"

staload "./string.sats"

extern castfn ssz2sz {n: int} (x: ssize_t(n)): size_t(n)

extern fun memmove(dst: ptr, src: ptr, size: ssize_t): void = "mac#"
extern fun memcmp(s1: ptr, s2: ptr, n: size_t): int = "mac#"

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
		val len1 = strnptr_length(str1)
		val len2 = strnptr_length(str2)
		val cmp = compare(len1, len2)
	in
		if cmp = 0 then
			memcmp(strnptr2ptr(str1), strnptr2ptr(str2), ssz2sz(len1))
		else
			cmp
	end
/*
Old implementation, too many allocations
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
*/
implement string_equal(str1, str2) = string_compare(str1, str2) = 0

extern castfn string_stack2string {n: nat | n > 0} (s: string(n)): strnptr11(n)

fun {a:viewt@ype} forget (x: !a >> a?): void = let prval () = $UNSAFE.castvwtp2void(x) in end

implement string_compare_stack(str, s) =
	let
		val str2 = string_stack2string(s)
		val res = string_compare(str, str2)
	in
		forget(str2);
		res
	end
/*
Old implementation
implement string_compare_stack(str, s) =
	let
		val s = string_new(s)
		val res = string_compare(str, s)
	in
		string_free(s);
		res
	end
*/
implement string_equal_stack(str, s) = string_compare_stack(str, s) = 0

implement string_print(str) = print_strnptr(str)

/// XXX !!!!!!! THIS IS NOT SAFE !!!!!!!
// ATS thinks that the string is still the same size, but I just don't know
// how to tell it that the size is decreased when calling an external C function
implement string_cut_head(s) =
	memmove(strnptr2ptr(s), ptr_succ<char>(strnptr2ptr(s)), strnptr_length(s))

implement string_free(str) = strnptr_free(str)
