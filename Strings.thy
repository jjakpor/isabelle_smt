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
  by (metis append_take_drop_id drop_eq_Nil int_nat_eq length_drop length_take linorder_not_le min_def nat_0_iff nat_minus_as_int not_less_iff_gr_or_eq take_eq_Nil2 zless_nat_conj)

theorem substr_correct2:
fixes m::"int" and n::"int"
shows "\<not>(0\<le>m \<and> m < (int (length w)) \<and> 0 < n) \<Longrightarrow> (str_substr w m n = \<epsilon>)"
  unfolding fac_def by auto
  

abbreviation str_prefixof:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_prefixof \<equiv> Words.is_prefix"
abbreviation str_suffixof:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_suffixof \<equiv> Words.is_suffix"

(* Correctness of prefixof: \<lbrakk>str.prefixof\<rbrakk>(v, w) = true iff w = vx₂ for some word x *)
theorem prefixof_correct: "str_prefixof v w \<longleftrightarrow> (EX x. w = v@x)"
  by (simp add: prefix_iff_startswith)


(* Correctness of suffixof: \<lbrakk>str.suffixof\<rbrakk>(v, w) = true iff w = xv₂ for some word x *)
theorem suffix_correct: "str_suffixof v w \<longleftrightarrow> (EX x. w = x@v)"
  by (simp add: suffix_iff_endswith) 

abbreviation str_contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "str_contains \<equiv> Words.contains"


value "List.enumerate 0 ''abc''"
  

abbreviation str_indexof:: "'a word \<Rightarrow> 'a word \<Rightarrow> int \<Rightarrow> int" 
  where "str_indexof h n s \<equiv> if s \<ge> 0 then (case find_index (drop (nat s) h) n of Some r \<Rightarrow> (int r+s) | option.None \<Rightarrow> -1) else (-1)"


lemma x:"str_indexof h n s = i \<and> i\<ge>0 \<Longrightarrow> i-s \<ge> 0"
  unfolding find_index_def
  apply(auto)
  by (simp add: option.split_sel_asm)


(* This is what SMT-LIB states but it is invalid
   lemma "str_contains w v \<and> i \<ge> 0 \<Longrightarrow> (str_indexof w v i) \<ge> 0

  nitpick finds counterexample.
  Instead, it is supposed to be the following:
*)
lemma indexof_if_suffix_contains: assumes "i\<ge>0 \<and> str_contains (drop (nat i) w) v" shows  "(str_indexof w v i) \<ge> i"
  using assms contains_iff_find_index by force




theorem indexof_correct_1:
  fixes i::"int"
  shows "i\<ge>0 \<and> i \<le> int (length w) \<and> str_contains (drop (nat i) w) v \<Longrightarrow> EX n x y. ((str_indexof w v i) = n \<and>  w = x@v@y \<and> (int (length x)) = n)"
  apply(auto simp add: option.case_eq_if)
   apply (simp add: contains_iff_find_index)
  using find_index_of_suffix  by (metis int_nat_eq nat_le_iff of_nat_add)

theorem indexof_correct2: 
   "(i < 0 \<or> \<not>(str_contains (drop (nat i) w) v)) \<Longrightarrow> (str_indexof w v i) = -1"
  using contains_iff_find_index by fastforce
 
  

(* Regular Expression Functions *)

abbreviation str_in_re:: "'a::linorder word \<Rightarrow> 'a regex \<Rightarrow> bool" where "str_in_re w R \<equiv> re_contains w R"

theorem in_re_correct:"str_in_re w R \<longleftrightarrow> w \<in> (lang R)"
  by (auto simp add: re_contains_def derivative_correctness)


abbreviation str_to_re:: "'a::linorder word \<Rightarrow> 'a regex" where "str_to_re w \<equiv> regex.Const w"
theorem to_re_correct: "lang (str_to_re w) = {w}" by simp

abbreviation re_none:: "'a::linorder regex" where "re_none \<equiv> regex.None"
theorem re_none_correct: "lang re_none = {}" by simp

abbreviation re_allchar:: "'a::linorder regex" where "re_allchar \<equiv> regex.Any"
theorem re_allchar_correct: "lang re_allchar = {w. (length w) = 1}" by simp
  
(* missing:  re_all*)

abbreviation re_concat:: "'a::linorder regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex"  where "re_concat r1 r2 \<equiv> RegEx.re_concat r1 r2"
theorem re_concat_correct: "(lang (re_concat r e)) = {x@y|x y. x \<in> (lang r) \<and> y \<in> (lang e)}" 
  by (simp add: Regular.concat_def re_concat_correct)

abbreviation re_union:: "'a::linorder regex \<Rightarrow> 'a regex \<Rightarrow> 'a regex" where "re_union r1 r2 \<equiv> RegEx.re_union r1 r2"
theorem re_union_correct: "lang (re_union r e) = {w|w. w \<in> (lang r) \<or> w \<in> (lang e)}"
  by (simp add: Un_def re_union_correct)


abbreviation re_star:: "'a::linorder regex \<Rightarrow>'a regex" where "re_star r \<equiv> RegEx.re_star r"
theorem re_star_correct: "((lang (re_star r)) = k) \<Longrightarrow> \<epsilon> \<in> k \<and> (\<exists> e. (concat (lang r) k) \<subseteq> k)"
  by (auto simp add: re_star_correct concat_star_subset)
  
abbreviation re_plus:: "'a::linorder regex \<Rightarrow> 'a regex" where "re_plus r \<equiv> RegEx.re_plus r"
theorem re_plus_correct: "lang (re_plus r) = lang (re_concat r (re_star r))" by (simp add: re_plus_def)

(* missing: re_inter, re_com, re_diff, re_plus, re_opt, re_range, re_pow, re_loop *)
fun re_range:: "'a::linorder word \<Rightarrow> 'a::linorder word \<Rightarrow> 'a regex" where 
"re_range (l#\<epsilon>) (u#\<epsilon>) = RegEx.re_range l u"|
"re_range _ _ = RegEx.None"

theorem re_range_correct1: "(length l) = 1 \<and> (length u) = 1 \<Longrightarrow> (lang (re_range l u)) = {v#\<epsilon>|v ll uu. l=(ll#\<epsilon>) \<and> u = (uu#\<epsilon>) \<and> ll \<le> v \<and> v \<le> uu}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
  by (auto split: if_splits)

theorem re_range_correct2: "(length l) \<noteq> 1 \<or> (length u) \<noteq> 1 \<Longrightarrow> (lang (re_range l u)) = {}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
  by (auto split: if_splits)
  


end