#include "share/atspre_staload.hats"
// #define ATS_DYNLOADFLAG 0

staload "./dictionary.sats"
staload "./pattern.sats"
staload "./phrase.sats"
staload "./rule.sats"
staload "./skeleton.sats"
staload "./string.sats"

overload close with fileref_close
overload is_some with option_vt_is_some


viewtypedef Grammar = @[Rule][12]

#define EXP_NUM 0
#define EXP_STR 1
#define EXP_PAT 2
#define EXP_SKE 3
#define EXP_RUL 4

dataviewtype exp(int) =
	| num(EXP_NUM) of int
	| str(EXP_STR) of String
	| pat(EXP_PAT) of Pattern
	| ske(EXP_SKE) of Skeleton
	| rul(EXP_RUL) of Rule

viewtypedef Exp = [n: nat] exp(n)

#define :: list_vt_cons

fun lookup(symbol: !String, dict: !Dictionary): Option_vt(Phrase) =
	// It's very important to copy the expression in case there are more than one holes that refer
	// to the same pattern variable. For example: ?x => :x :x ;
	case+ dict of
	| list_vt_cons(t, ds) when t.0 = symbol => Some_vt(gcopy(t.1))
	| list_vt_cons(_, ds) => lookup(symbol, ds)
	| list_vt_nil() => None_vt()

/*
fn is_balanced {n: nat | n > 0} (ph: !Phrase, symbols: phrase(n)): bool =
	let
		val+ ~list_vt_cons(x, xs) = symbols
		val o = ocurrences(ph, x)

		fun loop(ph: !Phrase, symbols: Phrase): bool =
			case+ symbols of
			| ~list_vt_nil() => true
			| ~list_vt_cons(x, xs) =>
				let
					val ocur = ocurrences(ph, x)
				in
					gfree(x);
					if ocur = o then
						loop(ph, xs)
					else (
						gfree(xs);
						false
					)
				end
	in
		gfree(x);
		loop(ph, xs)
	end
*/


// Returns (if successful) a pair containing a dictionary and the tail of the expression that was not matched
fun match(ph: Phrase, pat: !Pattern): Option_vt(@(Dictionary, Phrase)) =
	let
		// TODO Add a new argument that keeps track of the balanced symbols using a stack (temp is unused right now)
		fun loop2 {n: nat} (pat: !Pattern, ph: Phrase, dict: dictionary(n), temp: Phrase): Option_vt(@(Dictionary, Phrase)) = (
			(*
				TODO: to be implemented
					- the case for ...
					- the case for balanced symbols
			*)
			case+ pat of

			| pat_symbol(s)::ps => (
				case+ ph of
				| ~x::xs when x = s => (gfree(x); loop2(ps, xs, dict, temp))
				| _ => (
					gfree(ph);
					gfree(dict);
					gfree(temp);
					None_vt()
				)
			)

			| pat_atom(a)::ps => (
				case+ ph of
				| ~x::xs =>
					let
						val opt = lookup(a, dict)
					in
						case+ opt of
						// If the symbol is not in the dictionary, add it
						| ~None_vt() => loop2(ps, xs, list_vt_cons((gcopy(a), x::list_vt_nil()), dict), temp)
						// If the symbol is defined, compare the definitions and assert they are the same
						| ~Some_vt(def) =>
							let
								val def' = $list_vt{String}(x)
								val eq = def = def'
							in
								gfree(def);
								gfree(def');

								if eq then
									loop2(ps, xs, dict, temp)
								else (
									gfree(xs);
									gfree(temp);
									gfree(dict);
									None_vt()
								)
							end
					end
				| _ => (
					gfree(ph);
					gfree(dict);
					gfree(temp);
					None_vt()
				)
			)

			| pat_under()::ps => (
				case+ ph of
				| ~x::xs => (gfree(x); loop2(ps, xs, dict, temp))
				| _ => (
					gfree(ph);
					gfree(temp);
					gfree(dict);
					None_vt()
				)
			)

			// This is the "base" case of the mult pattern, successful recursive calls to match that
			// handle this pattern will end here
			| pat_mult(m)::list_vt_nil() => (
				gfree(temp);
				Some_vt(@(list_vt_cons(@(gcopy(m), ph), dict), list_vt_nil))
			)

			| pat_mult(m)::_ => (
				let
					// This function examines the pattern to check for a delimiter and splits it in two
					// at that specific symbol. XXX the case [1] can be removed if everything is handled
					// from within this function and thus speeding up the program
					fun create_subpattern {n: nat | n > 0} (pat: !Pattern, temp: pattern(n)): [m: int | m > 0] (pattern(m), Pattern) =
						// TODO handle here the case for the '_' and the '...'
						case+ pat of
						| list_vt_nil() => (temp, list_vt_nil())
						| list_vt_cons(pat_symbol(x), xs) => (list_vt_cons(pat_symbol(gcopy(x)), temp), pattern_copy(xs))
						| list_vt_cons(pat_bal(x), xs) => (list_vt_cons(pat_bal(gcopy(x)), temp), pattern_copy(xs))
						// Don't add successive mults without a proper delimiter as they are ambiguous
						| list_vt_cons(pat_mult(_), xs) => create_subpattern(xs, temp)
						| list_vt_cons(p, xs) => create_subpattern(xs, list_vt_cons(gcopy(p), temp))

					// Head could be multiple elements, not just one
					val+ @(pat_head, pat_tail) = create_subpattern(pat, $list_vt(pat_mult(gcopy(m))))
				in
					// XXX [1]
					case+ pat_head of
					// If the last (first, as it is reversed) element in the subpattern is a symbol
					// then find it in the phrase and cut the phrase at that position.
					| list_vt_cons(pat_symbol(last), cs) =>
						let
							fun create_subphrase(ph: Phrase, temp: Phrase, last: !String): @(Phrase, Phrase) =
								case+ ph of
								| ~list_vt_nil() => (temp, list_vt_nil())
								| ~list_vt_cons(x, xs) when x = last => (list_vt_cons(x, temp), xs)
								| ~list_vt_cons(x, xs) => create_subphrase(xs, list_vt_cons(x, temp), last)

							val+ @(ph_head, ph_tail) = create_subphrase(ph, list_vt_nil, last)

							val opt = match(ph_head, pat_head)
						in
							gfree(pat_head);

							case+ opt of
							| ~Some_vt(@(d,t)) =>
								let
									// d is the resulting dictionary from matching the subphrase that was cut
									// d has to contain something and t has to be empty
									val () = assertloc(length(d) > 0)
									val () = assertloc(length(t) = 0)

									// Since everything was reversed, definitions within the dictionary that
									// were created in the recursive call to match are also reversed so they
									// have to be reversed again
									implement list_vt_app$fwork<@(String, Phrase)>(t) = t.1 := list_vt_reverse(t.1)
									val () = list_vt_app(d)

									val dict = list_vt_append(d, dict)
									val res = loop2(pat_tail, ph_tail, dict, temp)
								in
									gfree(pat_tail);
									gfree(t);
									res
								end
							| ~None_vt() => (
								gfree(pat_tail);
								gfree(ph_tail);
								gfree(dict);
								gfree(temp);
								None_vt()
							)
						end
					// TODO copypaste the match for pat_bal()
					// | list_vt_cons(pat_bal(last), _) =>

					// If the last element was not a symbol, just reverse the phrase and match
					// No recursive call is needed
					| list_vt_cons(_, _) =>
						let
							val () = assertloc(length(pat_tail) = 0)

							val rev = list_vt_reverse(ph)
							val- ~Some_vt(@(d, t)) = match(rev, pat_head)

							val () = assertloc(length(d) > 0)
							val () = assertloc(length(t) = 0)

							// Just like the other case, reverse the definitions in the dictionary
							implement list_vt_app$fwork<@(String, Phrase)>(t) = t.1 := list_vt_reverse(t.1)
							val () = list_vt_app(d)

							val dict = list_vt_append(d, dict)
						in
							gfree(pat_tail);
							gfree(temp);
							gfree(pat_head);
							// Unlike the previous case, the phrase to be reduced has no tail since it
							// wasn't cut because no delimiter symbol was found, so there's no recursive
							// call here
							Some_vt(@(dict, t))
						end
				end
			)

			// If the pattern is empty, any phrase will match it. Considering that it is impossible
			// to add a rule with an empty pattern, this branch will only be reached when the matcher
			// has been successful on every recursive call
			| list_vt_nil() => (gfree(temp); Some_vt(@(dict, ph)))

			| _ => (gfree(temp); gfree(ph); gfree(dict); None_vt())
		)
	in
		if length(ph) >= pattern_length(pat) then
			loop2(pat, ph, dictionary_new(), phrase_new())
		else (
			gfree(ph);
			None_vt()
		)
	end

extern fun reduce: (Phrase, !List_vt(Rule)) -> Phrase

fn instantiate(dict: !Dictionary, ske: !Skeleton, rules: !List_vt(Rule)): Option_vt(Phrase) =
	let
		val phr: Phrase = phrase_new()

		fun loop(ske: !Skeleton, dict: !Dictionary, ph: Phrase, rules: !List_vt(Rule)): Option_vt(Phrase) =
			case+ ske of
			| ske_symbol(s)::ss => loop(ss, dict, ph', rules) where {
				val ph' = list_vt_append(gcopy(s)::list_vt_nil, ph)
			}
			| ske_hole(s)::ss => (
				case+ lookup(s, dict) of
				// TODO way too many (two, to be exact) reverses
				| ~Some_vt(def) => loop(ss, dict, list_vt_append(list_vt_reverse(def), ph), rules)
				| ~None_vt() => (
					gfree(ph);
					None_vt()
				)
			)
			| ske_reduce(s)::ss => (
				case+ lookup(s, dict) of
				// TODO reduce this expression
				| ~Some_vt(def) => loop(ss, dict, list_vt_append(reduce(list_vt_reverse(def), rules), ph), rules)
				| ~None_vt() => (gfree(ph); None_vt())
			)
			// TODO See if its possible to reverse ph as we're iterating
			// the skeleton data structure for performance, instead of
			// reversing it here
			| list_vt_nil() => Some_vt(list_vt_reverse(ph))
	in
		loop(ske, dict, phr, rules)
	end


extern castfn sz2i {n: int} (x: ssize_t(n)): int(n)

fn option_vt_print(x: !Option_vt(int)): void =
	case+ x of
	| Some_vt(f) => (print("Some "); print(f))
	| None_vt() => print("None")

extern fun atoi(s: !Strnptr): int = "mac#"

fn {a: viewt@ype} stream_vt_uncons(st: stream_vt(a)): Option_vt(@(a, stream_vt(a))) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_cons(x, xs) => Some_vt(@(x, xs))
		| ~stream_vt_nil() => None_vt()
	end

fn strnptr2int {m: nat | m > 0} (s: strnptr(m)): Option_vt(int) =
	let
		val len: int(m) = sz2i(length(s))
		fun loop {n: nat | n < m} (s: !strnptr(m), i: int(n)): bool =
			if isdigit(strnptr_get_at_size(s, i2sz(i))) then
				if i + 1 < len then
					loop(s, i + 1)
				else
					true
			else
				false
	in
		if loop(s, 0) then
			let
				val n = atoi(s)
			in
				strnptr_free(s);
				Some_vt(n)
			end
		else (
			strnptr_free(s);
			None_vt()
		)
	end

fn parse_string(st: stream_vt(String)): Option_vt(@(exp(1), stream_vt(String))) =
	let
		val st' = stream_vt_uncons<String>(st)
	in
		case+ st' of
		| ~Some_vt(t) => Some_vt(@(str(t.0), t.1))
		| ~None_vt() => None_vt()
	end

fn parse_string_matching(st: stream_vt(String), match: string): Option_vt(@(exp(1), stream_vt(String))) =
	let
		val st = stream_vt_uncons<String>(st)
	in
		case+ st of
		| ~Some_vt(t) =>
			let
				val st = t.1
				val s = t.0
				val d = strnptr_copy(s)
				val e = strnptr2string(d)
				val eq = eq_string_string(e, match)
				val () = strptr_free($UNSAFE.castvwtp0{strptr} e)
			in
				if eq then (
					Some_vt(@(str(s), st))
				) else (
					stream_vt_free(st);
					strnptr_free(s);
					None_vt()
				)
			end
		| ~None_vt() => None_vt()
	end

fn parse_int(st: stream_vt(String)): Option_vt(@(exp(EXP_NUM), stream_vt(String))) =
	let
		val st' = stream_vt_uncons<String>(st)
	in
		case+ st' of
		| ~Some_vt(t) when length(t.0) > 0 =>
			let
				val t_st: stream_vt(String) = t.1
				val t_s: Strnptr = t.0
				val n_opt = strnptr2int(t_s)
			in
				case+ n_opt of
				| ~Some_vt(n) => Some_vt(@(num(n), t_st))
				| ~None_vt() => (
					stream_vt_free(t_st);
					None_vt()
				)
			end
		| ~Some_vt(t) => (
			strnptr_free(t.0);
			stream_vt_free(t.1);
			None_vt()
		)
		| ~None_vt() => None_vt()
	end

fn parse_pat(st: stream_vt(String)): Option_vt(@(exp(EXP_PAT), stream_vt(String))) =
	let
		fun loop {n: nat} (st: stream_vt(String), p: pattern(n)): Option_vt(@(exp(EXP_PAT), stream_vt(String))) =
			let
				val st = stream_vt_uncons<String>(st)
			in
				case+ st of
				| ~None_vt() => (
					pattern_free(p);
					None_vt()
				)
				| ~Some_vt(t) =>
					let
						val st = t.1
						val s = t.0
						val d = strnptr_copy(s)
						val e = strnptr2string(d)
						val eq = eq_string_string(e, "=>")
						// So yeah... ATS allows a leak here. This cast has to be done
						val () = strptr_free($UNSAFE.castvwtp0{strptr}(e))
					in
						if eq then (
							strnptr_free(s);
							Some_vt(@(pat(list_vt_reverse(p)), st)) // Again... list_vt_reverse here too
						) else (
							loop(st, list_vt_cons(pat_from_string(s), p))
						)
					end
			end
	in
		loop(st, $list_vt{Pat}())
	end

fn parse_skeleton(st: stream_vt(String)): Option_vt(@(exp(EXP_SKE), stream_vt(String))) =
	let
		fun loop {n: nat} (st: stream_vt(String), sk: skeleton(n)): Option_vt(@(exp(EXP_SKE), stream_vt(String))) =
			let
				val st = stream_vt_uncons<String>(st)
			in
				case+ st of
				| ~None_vt() => (
					skeleton_free(sk);
					None_vt()
				)
				| ~Some_vt(t) =>
					let
						val st = t.1
						val s = t.0
						val d = strnptr_copy(s)
						val e = strnptr2string(d)
						val eq = eq_string_string(e, ";")
						val () = strptr_free($UNSAFE.castvwtp0{strptr}(e))
					in
						if eq then (
							strnptr_free(s);
							Some_vt(@(ske(list_vt_reverse(sk)), st))
						) else (
							loop(st, list_vt_cons(ske_from_string(s), sk))
						)
					end
			end
	in
		loop(st, $list_vt{Ske}())
	end

fun streamize_fileref_word(file: FILEref): stream_vt(String) =
	$ldelay(
		if fileref_is_eof(file) then
			stream_vt_nil()
		else
			let
				implement fileref_get_word$isalpha<>(c) =
					not (c = ' ' || c = '\t' || c = '\n' || c = '\v' || c = '\f' || c = '\r')
				val st = strptr2strnptr(fileref_get_word(file))
			in
				if strnptr_isnot_null(st) * (strnptr_length(st) > 0) then
					stream_vt_cons(st, streamize_fileref_word(file))
				else (
					strnptr_free(st);
					stream_vt_nil()
				)
			end
	)



fn print_ex(e: !Exp): void =
	case+ e of
	| num(n) => print(n)
	| str(s) => print(s)
	| pat(p) => pattern_print(p)
	| ske(s) => skeleton_print(s)
	| rul(r) => rule_print(r)

fn free_ex(e: Exp): void =
	case+ e of
	| ~num(n) => ()
	| ~str(s) => gfree(s)
	| ~pat(p) => gfree(p)
	| ~ske(s) => gfree(s)
	| ~rul(r) => gfree(r)

/*
fun free_exp(e: List_vt(Exp)): void =
	case+ e of
	| ~list_vt_cons(~num(_), es) => free_exp(es)
	| ~list_vt_cons(~str(s), es) => (gfree(s); free_exp(es))
	| ~list_vt_cons(~pat(p), es) => (gfree(p); free_exp(es))
	| ~list_vt_cons(~ske(s), es) => (gfree(s); free_exp(es))
	| ~list_vt_cons(~rul(r), es) => (gfree(r); free_exp(es))
	| ~list_vt_nil() => ()
*/

macdef parse_keyword = parse_string_matching

// The delicate art of working with linear streams
fn stream_vt_peek(st: stream_vt(String)): @(Option_vt(String), stream_vt(String)) =
	let
		val s = !st
	in
		case+ s of
		| ~stream_vt_nil() => @(None_vt(), $ldelay(stream_vt_nil()))
		| ~stream_vt_cons(x, xs) => @(Some_vt(gcopy(x)), $ldelay(stream_vt_cons(x, xs), (~xs; gfree(x))))
	end

// Don't look
fn parse_rule(st: stream_vt(String)): Option_vt(@(exp(4), stream_vt(String))) =
	let
		val level = parse_int(st)
	in
		case+ level of
		| ~None_vt() => (/*println!("Expected rule level (integer)");*/ None_vt())
		| ~Some_vt(t) =>
			let
				val l = t.0
				val prec = parse_int(t.1)
			in
				case+ prec of
				| ~None_vt() => (println!("Expected rule precedence (integer)"); free_ex(l); None_vt())
				| ~Some_vt(t) =>
					let
						val p = t.0
						val name = parse_string(t.1)
					in
						case+ name of
						| ~None_vt() => (println!("Expected rule name"); free_ex(l); free_ex(p); None_vt())
						| ~Some_vt(t) =>
							let
								val n = t.0
								val colon = parse_keyword(t.1, ":")
							in
								case+ colon of
								| ~None_vt() => (println!("Expected colon (:)"); free_ex(l); free_ex(p); free_ex(n); None_vt())
								| ~Some_vt(t) =>
									let
										val+ ~str(col) = t.0
										val patt = parse_pat(t.1)
									in
										strnptr_free(col);
										case+ patt of
										| ~None_vt() => (free_ex(l); free_ex(p); free_ex(n); None_vt())
										| ~Some_vt(t) =>
											let
												val+ ~pat(pt) = t.0
												val skel = parse_skeleton(t.1)
											in
												case+ skel of
												| ~None_vt() => (free_ex(l); free_ex(p); free_ex(n); pattern_free(pt); None_vt())
												| ~Some_vt(t) =>
													let
														val+ ~num(l) = l
														val+ ~num(p) = p
														val+ ~str(n) = n
														val+ ~ske(sk) = t.0
														val rule = @{
															level = l,
															precedence = p,
															name = n,
															pattern = pt,
															skeleton = sk
														}: Rule
													in
														Some_vt(@(rul(rule), t.1))
													end
											end
									end
							end
					end

			end
	end

// Try to match the phrase against one specific rule.
// Portions of that phrase are also allowed to match.
fn try_rule(ph: !Phrase, rule: !Rule, rules: !List_vt(Rule)): Option_vt(Phrase) =
	let
		val copy = gcopy(ph)

		fun loop(ph: Phrase, rule: !Rule, tmp: Phrase, rules: !List_vt(Rule)): Option_vt(Phrase) =
			case+ ph of
			| ~list_vt_nil() => (gfree(tmp); None_vt())
			| list_vt_cons(p, ps) =>
				let
					val p = gcopy(p)
					val cp = gcopy(ps)
					val opt = match(ph, rule.pattern)
				in
					case+ opt of
					| ~None_vt() => loop(cp, rule, tmp, rules) where {
						val tmp = list_vt_cons(p, tmp)
					}
					| ~Some_vt(t) =>
						let
							val dict = t.0
							val tail = t.1
							val final = instantiate(dict, rule.skeleton, rules)
						in
							gfree(p);
							gfree(cp);
							dictionary_free(dict);
							case+ final of
							| ~None_vt() => (
								gfree(tmp);
								gfree(tail);
								None_vt()
							)
							// XXX check if the phrase p here is an intrinsic
							| ~Some_vt(p) =>
								let
									val tail = list_vt_append(p, tail)
									val head = list_vt_reverse(tmp)
								in
									Some_vt(list_vt_append(head, tail))
								end

						end
				end
	in
		loop(copy, rule, phrase_new(), rules)
	end

// For each rule, try to match the phrase against it
// If successful returns a tuple with the name of the rule that was matched and the
// reduced phrase.
fun try_rules(ph: !Phrase, rules: !List_vt(Rule)): Option_vt(@(String, Phrase)) =
	case+ rules of
	| list_vt_nil() => None_vt()
	| list_vt_cons(r, rs) =>
		let
			val opt = try_rule(ph, r, rules)
		in
			case+ opt of
			| ~None_vt() => (
				try_rules(ph, rs)
			)
			| ~Some_vt(e) => Some_vt(@(gcopy(r.name), e))
		end



// XXX see if it's possible to redo this function without copying the rules list and instead
// take out the rules that match
fn filter_rules(rules: !List_vt(Rule), level: int): List_vt(Rule) =
	let
		fun loop {n: nat} (rules: !List_vt(Rule), ac: list_vt(Rule, n)): List_vt(Rule) =
			case+ rules of
			| list_vt_nil() => ac
			| list_vt_cons(r, rs) when r.level = level => loop(rs, list_vt_cons(rule_copy(r), ac))
			| list_vt_cons(_, rs) => loop(rs, ac)
	in
		list_vt_reverse(loop(rules, $list_vt{Rule}()))
	end


fun add_rule {n: nat} (rules: list_vt(Rule, n), rule: Rule): list_vt(Rule, n + 1) =
	case+ rules of
	| list_vt_cons(r, rs) when rule.precedence > r.precedence => list_vt_cons(rule, rules)
	| ~list_vt_cons(r, rs) => list_vt_cons(r, add_rule(rs, rule))
	| ~list_vt_nil() => $list_vt{Rule}(rule)


fun stream_vt_skip_until {n: int | n > 0} (st: stream_vt(String), until: string(n)): Option_vt(stream_vt(String)) =
	let
		val opt = stream_vt_uncons<String>(st)
	in
		case+ opt of
		| ~None_vt() => None_vt()
		| ~Some_vt(t) =>
			let
				val s = t.0
				val st = t.1
				val b = s = until
			in
				gfree(s);
				if b then
					Some_vt(st)
				else
					stream_vt_skip_until(st, until)
			end
	end

fn skip_comment(st: stream_vt(String)): Option_vt(stream_vt(String)) = stream_vt_skip_until(st, "*/")

viewtypedef Parser(a: viewt@ype) = stream_vt(String) -> Option_vt(@(a, stream_vt(String)))
viewtypedef ParserT(a: viewt@ype) = stream_vt(String) -> a

extern fun parse_file: ParserT(List_vt(Rule))
implement parse_file(st) =
	let
		fun loop {n: nat} (st: stream_vt(String), rules: list_vt(Rule, n)): List_vt(Rule) =
			let
				val+ (t, st) = stream_vt_peek(st)
			in
				case+ t of
				| ~None_vt() => (~st; rules)
				| ~Some_vt(symbol) when symbol = "/*" =>
					let
						val opt = skip_comment(st)
					in
						gfree(symbol);
						case+ opt of
						| ~None_vt() => rules
						| ~Some_vt(st) => loop(st, rules)
					end

				| ~Some_vt(symbol) => (
					let
						val opt = parse_rule(st)
					in
						gfree(symbol);
						case+ opt of
						| ~None_vt() => rules
						| ~Some_vt(t) =>
							let
								val+ ~rul(r) = t.0
								val st = t.1
							in
								if rule_is_valid(r) then
									loop(st, add_rule(rules, r))
								else (
									// If a rule is not valid, undo everything
									gfree(r);
									loop(st, rules)
								)
							end
					end
				)

			end
	in
		loop(st, $list_vt{Rule}())
	end

implement reduce(ph, rules) =
	let
		val ph_opt = try_rules(ph, rules)
	in
		case+ ph_opt of
		| ~Some_vt(t) =>
			let
				val name = t.0
				val ph' = t.1
			in
				gprintln!(ph);
				gfree(name);
				gfree(ph);
				reduce(ph', rules)
			end
		| ~None_vt() => ph
	end

implement main0(argc, argv) =
	let
		val file =
			if argc > 1 then
				let
					val file_opt = fileref_open_opt(argv[1], file_mode_r)
				in
					case+ file_opt of
					| ~None_vt() => stdin_ref
					| ~Some_vt(f) => f
				end
			else
				stdin_ref

		val stream = streamize_fileref_word(file)

		implement list_vt_freelin$clear<Rule>(r) = $effmask_all(rule_free(r))

		// val grammar = some array of rules

		val rules = parse_file(stream)

		val level_0 = filter_rules(rules, 0)
		val level_1 = filter_rules(rules, 1)
		// val grammar = arrayptr_make_uninitized<List_vt(Rule)>(i2sz 12)
		// val () = arrayptr_set_at_gint(grammar, 0, level_0)
		// implement array_uninitize$clear<List_vt(Rule)>(i, x) = list_vt_freelin<Rule>(x)
		// val () = arrayptr_freelin(grammar, i2sz 12)
		val init0 = $list_vt{String}(string_new("main"))
		val init1 = $list_vt{String}(string_new("main"))

		// Phrase reduction loop
		val () = println!("Reductions:")
		val exp0 = reduce(init0, level_0)
		val exp1 = reduce(init1, level_1)
	in
		gprintln!("\nFinal expression\n0: ", exp0, "\n1: ", exp1);
		list_vt_freelin(rules);
		gfree(exp0);
		gfree(exp1);
		list_vt_freelin(level_0);
		list_vt_freelin(level_1);
		close(file)
	end
