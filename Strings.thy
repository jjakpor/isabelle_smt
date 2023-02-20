theory Strings
  imports Core "strings/RegEx" "strings/Words"  "HOL-Library.Numeral_Type"
begin

typedef uc = "{x::nat. x\<le> 196607}" morphisms as_nat uc_char by auto
setup_lifting type_definition_uc
code_datatype uc_char


instantiation uc::linorder begin
lift_definition less_eq_uc:: "uc\<Rightarrow>uc\<Rightarrow>bool" is "(\<le>)::(nat \<Rightarrow> nat \<Rightarrow> bool)" .
lift_definition less_uc::"uc\<Rightarrow>uc\<Rightarrow>bool" is "(<)::(nat \<Rightarrow> nat \<Rightarrow> bool)".
instance proof
  fix x y z:: uc
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)" using less_eq_uc.rep_eq less_uc.rep_eq by auto
  show "x\<le>x"  by (simp add: less_eq_uc.rep_eq)
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"  using less_eq_uc.rep_eq by auto
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"  by (simp add: as_nat_inject less_eq_uc.rep_eq)
  show "x \<le> y \<or> y \<le> x"  using less_eq_uc.rep_eq by auto 
qed
end


instantiation uc::equal begin 
lift_definition equal_uc:: "uc\<Rightarrow>uc\<Rightarrow>bool" is "\<lambda> a b. (as_nat a) = (as_nat b)" .
instance  by (standard, auto simp add: equal_uc_def as_nat_inject)
end



type_synonym uc_string = "uc word"

definition UC:: "uc_string set" where "UC = {w. True}"
lemma "UNIV = UC"  by (simp add: UC_def)


(* 
This is the interface between SMT-LIB and the underlying the theory of strings.
It contains mappings from SMT-LIB predicates/functions to the corresponding formalization/implementation.

Predicates in SMT-LIB are defined over integers and string, whereas in the corresponding Isabelle
theories, they are defined naturally over natural number and string.
The conversion between integers and naturals as well as handling of edge cases 
(as explained in the SMT-LIB standard) is performed here.

Pure string predicates are defined in "strings/Words", regular expression in "strings/RegEx".
*)

abbreviation str_concat:: "uc_string \<Rightarrow> uc_string  \<Rightarrow> uc_string"  where "(str_concat) u v \<equiv> u@v" 


abbreviation str_len:: "uc_string \<Rightarrow> int" where  "str_len w \<equiv> of_nat (length w)"


abbreviation str_at:: "uc_string \<Rightarrow> int \<Rightarrow> uc_string" where "str_at w i \<equiv> if i \<ge> 0 then (at w (nat i)) else \<epsilon>"
abbreviation str_substr:: "uc_string \<Rightarrow> int \<Rightarrow> int \<Rightarrow> uc_string"  where "str_substr w m n \<equiv> if (n \<ge> 0 \<and> 0\<le>m \<and> ((nat m) \<le> (length w)-1)) then  fac w (nat m) (nat n) else \<epsilon>"

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
  

abbreviation str_prefixof:: "uc_string \<Rightarrow> uc_string \<Rightarrow> bool" where "str_prefixof \<equiv> Words.is_prefix"
abbreviation str_suffixof:: "uc_string \<Rightarrow> uc_string \<Rightarrow> bool" where "str_suffixof \<equiv> Words.is_suffix"

(* Correctness of prefixof: \<lbrakk>str.prefixof\<rbrakk>(v, w) = true iff w = vx₂ for some word x *)
theorem prefixof_correct: "str_prefixof v w \<longleftrightarrow> (EX x. w = v@x)"
  by (simp add: prefix_iff_startswith)


(* Correctness of suffixof: \<lbrakk>str.suffixof\<rbrakk>(v, w) = true iff w = xv₂ for some word x *)
theorem suffix_correct: "str_suffixof v w \<longleftrightarrow> (EX x. w = x@v)"
  by (simp add: suffix_iff_endswith) 

abbreviation str_contains:: "uc_string \<Rightarrow> uc_string \<Rightarrow> bool" where "str_contains \<equiv> Words.contains"


value "List.enumerate 0 ''abc''"
  

abbreviation str_indexof:: "uc_string \<Rightarrow> uc_string \<Rightarrow> int \<Rightarrow> int" 
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


abbreviation str_replace:: "uc_string \<Rightarrow> uc_string \<Rightarrow> uc_string \<Rightarrow> uc_string" where "str_replace \<equiv> replace"

theorem replace_correct1: "\<not>str_contains w v \<Longrightarrow> str_replace w v u = w" by (simp add: replace_id_if_not_contains)
theorem replace_correct2: "str_contains w v \<Longrightarrow> \<exists>x y. str_replace w v u = x@u@y \<and> w = x@v@y \<and> (\<forall> x'. (length x') < (length x) \<longrightarrow> (\<nexists>y'. w=x'@v@y'))"
  by(auto simp only: replace_first_factor)
  
  

(* Regular Expression Functions *)

abbreviation str_in_re:: "uc_string \<Rightarrow> uc regex \<Rightarrow> bool" where "str_in_re w R \<equiv> re_contains w R"

theorem in_re_correct:"str_in_re w R \<longleftrightarrow> w \<in> (lang R)"
  by (auto simp add: re_contains_def derivative_correctness)


abbreviation str_to_re:: "uc_string \<Rightarrow> uc regex" where "str_to_re w \<equiv> regex.Const w"
theorem to_re_correct: "lang (str_to_re w) = {w}" by simp

abbreviation re_none:: "uc regex" where "re_none \<equiv> regex.None"
theorem re_none_correct: "lang re_none = {}" by simp

abbreviation re_allchar:: "uc regex" where "re_allchar \<equiv> regex.Any"
theorem re_allchar_correct: "lang re_allchar = {w. (length w) = 1}" by simp
  
(* missing:  re_all*)

abbreviation re_concat:: "uc regex \<Rightarrow> uc regex \<Rightarrow> uc regex"  where "re_concat r1 r2 \<equiv> RegEx.re_concat r1 r2"
theorem re_concat_correct: "(lang (re_concat r e)) = {x@y|x y. x \<in> (lang r) \<and> y \<in> (lang e)}" 
  by (simp add: Regular.concat_def re_concat_correct)

abbreviation re_union:: "uc regex \<Rightarrow> uc regex \<Rightarrow> uc regex" where "re_union r1 r2 \<equiv> RegEx.re_union r1 r2"
theorem re_union_correct: "lang (re_union r e) = {w|w. w \<in> (lang r) \<or> w \<in> (lang e)}"
  by (simp add: Un_def re_union_correct)

abbreviation re_inter:: "uc regex \<Rightarrow> uc regex \<Rightarrow> uc regex" where "re_inter  \<equiv> RegEx.re_inter"
theorem re_inter_correct: "lang (re_inter r1 r2) = {w|w. w\<in> (lang r1) \<and> w \<in> (lang r2)}"
  by (auto simp add: re_inter_correct)
  

abbreviation re_star:: "uc regex \<Rightarrow>uc regex" where "re_star r \<equiv> RegEx.re_star r"
theorem re_star_correct: "((lang (re_star r)) = k) \<Longrightarrow> \<epsilon> \<in> k \<and> (concat (lang r) k) \<subseteq> k"
  by (auto simp add: re_star_correct concat_star_subset)
  
abbreviation re_plus:: "uc regex \<Rightarrow> uc regex" where "re_plus r \<equiv> RegEx.re_plus r"
theorem re_plus_correct: "lang (re_plus r) = lang (re_concat r (re_star r))" by (simp add: re_plus_def)

(* missing: re_inter, re_com, re_diff,  re_pow, re_loop *)
fun re_range:: "uc_string \<Rightarrow> uc_string \<Rightarrow> uc regex" where 
"re_range (l#\<epsilon>) (u#\<epsilon>) = RegEx.re_range l u"|
"re_range _ _ = RegEx.None"

theorem re_range_correct1: "(length l) = 1 \<and> (length u) = 1 \<Longrightarrow> (lang (re_range l u)) = {v#\<epsilon>|v ll uu. l=(ll#\<epsilon>) \<and> u = (uu#\<epsilon>) \<and> ll \<le> v \<and> v \<le> uu}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
  by (auto split: if_splits)

theorem re_range_correct2: "(length l) \<noteq> 1 \<or> (length u) \<noteq> 1 \<Longrightarrow> (lang (re_range l u)) = {}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
  by (auto split: if_splits)
  
abbreviation re_opt::"uc regex \<Rightarrow> uc regex" where "re_opt r \<equiv> re_union (Const \<epsilon>) r"

abbreviation re_comp::"uc regex \<Rightarrow> uc regex" where "re_comp \<equiv> RegEx.re_comp"
theorem re_comp_correct: "lang (re_comp r) = UC - (lang r)"
  by (auto simp add: re_comp_correct UC_def)

abbreviation re_diff:: "uc regex \<Rightarrow> uc regex \<Rightarrow> uc regex" where "re_diff \<equiv> RegEx.re_diff"
theorem re_diff_correct: "lang (re_diff r1 r2) = (lang r1) - (lang r2)" 
  by (simp add: re_diff_correct)

abbreviation re_pow::"nat \<Rightarrow> uc regex \<Rightarrow> uc regex" where "re_pow n r \<equiv> RegEx.re_pow r n"
theorem re_pow_correct1: "lang(re_pow 0 r) = {\<epsilon>}" by auto
theorem re_pow_correct2: "lang (re_pow (Suc n) r ) = concat (lang r) (lang (re_pow n r))"
  by (simp add: RegEx.re_concat_correct)

end