theory Strings
  imports Core "strings/RegEx" "strings/Words" 
begin

(* 
This is the interface between SMT-LIB and the underlying the theory of strings.
It contains mappings from SMT-LIB predicates/functions to the corresponding formalization/implementation.

Predicates in SMT-LIB are defined over integers and string, whereas in the corresponding Isabelle
theories, they are defined naturally over natural number and string.
The conversion between integers and naturals as well as handling of edge cases 
(as explained in the SMT-LIB standard) is performed here.

Pure string predicates are defined in "strings/Words", regular expression in "strings/RegEx".
*)

abbreviation str_concat:: "'a word \<Rightarrow> 'a word  \<Rightarrow> 'a word"  where "(str_concat) u v \<equiv> u@v" 
abbreviation str_len:: "'a word \<Rightarrow> int" where  "str_len w \<equiv> of_nat (length w)"


abbreviation str_at:: "'a word \<Rightarrow> int \<Rightarrow> 'a word" where "str_at w i \<equiv> if i \<ge> 0 then (at w (nat i)) else \<epsilon>"
abbreviation str_substr:: "'a word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> 'a word"  where "str_substr w m n \<equiv> if (n \<ge> 0 \<and> 0\<le>m \<and> ((nat m) \<le> (length w)-1)) then  fac w (nat m) (nat n) else \<epsilon>"

(* Correctness of at: \<lbrakk>str.at\<rbrakk>(w, n) = \<lbrakk>str.substr\<rbrakk>(w, n, 1) *)
theorem at_correct: "str_at w n = str_substr w n 1"
  unfolding fac_def at_def
  apply(auto)
  by (metis (no_types, lifting) append.simps(2) append_take_drop_id first.simps(1) first.simps(2) take_Suc take_eq_Nil2)


(* Correctness of substr: 
   - \<lbrakk>str.substr\<rbrakk>(w, m, n) is the unique word v such that
     for some words x and y
      - w = xvy
      - |x| = m
      - |y| = min(n, |w| - m) 
                                    if 0 <= m < |w| and 0 < n
    - \<lbrakk>str.substr\<rbrakk>(w, m, n) = \<epsilon>      otherwise
*)
theorem substr_correct1: 
  fixes m::"int" and n::"int"
  shows "0\<le>m \<and> m < (int (length w)) \<and> 0 < n \<Longrightarrow> (str_substr w m n = v \<Longrightarrow> (EX x y. (w = x@v@y \<and> ((int (length x)) = m) \<and> (int (length v)) = (min n ((int (length w)) - m)))))"
  unfolding fac_def
  apply(auto)+
  apply(simp add: int_eq_iff min_def)+
  apply(auto simp add:  int_ops(6) le_nat_iff)+
   apply (metis append.right_neutral append_take_drop_id le_nat_iff length_take less_le_not_le min_def nat_diff_distrib nat_int)
  by (smt (verit, best) append_take_drop_id le_nat_iff length_take min_def)

theorem substr_correct2:
fixes m::"int" and n::"int"
shows "\<not>(0\<le>m \<and> m < (int (length w)) \<and> 0 < n) \<Longrightarrow> (str_substr w m n = \<epsilon>)"
  unfolding fac_def by auto
  

abbreviation str_prefixof:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_prefixof \<equiv> Words.is_prefix"
abbreviation str_suffixof:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_suffixof \<equiv> Words.is_suffix"

(* Correctness of prefixof: \<lbrakk>str.prefixof\<rbrakk>(v, w) = true iff w = vx₂ for some word x *)
theorem prefixof_correct: "str_prefixof v w \<longleftrightarrow> (EX x. w = v@x)"
  unfolding is_prefix_def
  apply(auto)
  by (metis append_take_drop_id)

(* Correctness of suffixof: \<lbrakk>str.suffixof\<rbrakk>(v, w) = true iff w = xv₂ for some word x *)
theorem suffix_correct: "str_suffixof v w \<longleftrightarrow> (EX x. w = x@v)"
  unfolding  is_suffix_def is_prefix_def
  apply(auto)
  by (metis append_take_drop_id rev_append rev_rev_ident)

abbreviation str_contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_contains \<equiv> Words.contains"

(* Correctness of contains: \<lbrakk>str.contains\<rbrakk>(w, v) = true  iff  w = xvy₃ for some words x,y*)
theorem contain_correct: "Words.contains w v \<longleftrightarrow>(EX x y. w = x@v@y)"
  apply(induct w)
   apply(simp)
  apply(auto simp add: Strings.prefixof_correct)
     apply (metis append_Cons)
    apply (metis append_Cons)
   apply (metis append_Nil)
  by (metis append_eq_Cons_conv)
  

abbreviation str_indexof:: "'a word \<Rightarrow> 'a word \<Rightarrow> int \<Rightarrow> int" 
  where "str_indexof h n s \<equiv> if s \<ge> 0 then (case find (drop (nat s) h) n of Some r \<Rightarrow> (int r) | option.None \<Rightarrow> -1) else (-1)"

(* Regular Expression Functions *)

abbreviation str_in_re:: "'a word \<Rightarrow> 'a regex \<Rightarrow> bool" where "str_in_re w R \<equiv> contains w R"

theorem in_re_correct:"str_in_re w R \<longleftrightarrow> w \<in> (lang R)"
  by (auto simp add: contains_def norm_derivw_nullable_iff_contained)
  

abbreviation str_to_re:: "'a word \<Rightarrow> 'a regex" where "str_to_re w \<equiv> regex.Const w"
abbreviation re_none:: "'a regex" where "re_none \<equiv> regex.None"
abbreviation re_allchar:: "'a regex" where "re_allchar \<equiv> regex.Any"
(* missing:  re_all*)

abbreviation re_concat:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex"  where "re_concat r1 r2 \<equiv> Concat r1 r2"
abbreviation re_union:: "'a regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where "re_union r1 r2 \<equiv> Union r1 r2"
(* missing: re_inter, re_com, re_diff, re_plus, re_opt, re_range, re_pow, re_loop *)
abbreviation re_star:: "'a regex \<Rightarrow>'a regex" where "re_star r \<equiv> Star r"
abbreviation re_plus:: "'a regex \<Rightarrow> 'a regex" where "re_plus r \<equiv> Plus r"


end