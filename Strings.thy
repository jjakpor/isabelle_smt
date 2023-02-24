theory Strings
  imports Core "strings/RegEx" "strings/Words"  "HOL-Library.Numeral_Type"
begin



type_synonym uc_string = "196607 word"

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

abbreviation str_concat:: "uc_string \<Rightarrow> uc_string  \<Rightarrow> uc_string"  where "(str_concat) u v \<equiv> u\<cdot>v" 


abbreviation str_len:: "uc_string \<Rightarrow> int" where  "str_len w \<equiv> of_nat (length w)"


abbreviation str_at:: "uc_string \<Rightarrow> int \<Rightarrow> uc_string" where "str_at w i \<equiv> if i \<ge> 0 then (at w (nat i)) else \<epsilon>"
abbreviation str_substr:: "uc_string \<Rightarrow> int \<Rightarrow> int \<Rightarrow> uc_string"  where "str_substr w m n \<equiv> if (n \<ge> 0 \<and> 0\<le>m \<and> ((nat m) \<le> (length w)-1)) then  w[(nat m);(nat (m+n))] else \<epsilon>"


(* Correctness of at: \<lbrakk>str.at\<rbrakk>(w, n) = \<lbrakk>str.substr\<rbrakk>(w, n, 1) *)
theorem at_correct: "str_at w n = str_substr w n 1"
  apply(cases n)
   apply(simp add: Suc_nat_eq_nat_zadd1)
  apply (metis Suc_as_int add.commute at_is_fac_1 get_factor.simps plus_1_eq_Suc)
  by auto


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
  shows "0\<le>m \<and> m < (int (length w)) \<and> 0<n \<Longrightarrow> (str_substr w m n = v \<Longrightarrow> (EX x y. (w = x@v@y \<and> ((length x) = (nat m)) \<and>  (length v) = (min (nat n) ((length w) - (nat m))))))"
proof -
  assume a1: "0 \<le> m \<and> m < int (length w) \<and> 0 < n"
  assume a2: "(if 0 \<le> n \<and> 0 \<le> m \<and> nat m \<le> length w - 1 then w[nat m;nat (m + n)] else \<epsilon>) = v"
  from a1 a2 have "v =  w[nat m;nat (m + n)]" by (simp add: int_ops(6) nat_le_iff)
  then have a3:"v =  w[nat m;(nat m) + (nat n)]" using a1 nat_add_distrib by force

  from a1 a3 have "(nat m) < (length w) \<and> 0 < n \<and> v =  w[nat m;(nat m) + (nat n)]" by auto
  then have "\<exists> x y. w = x\<cdot>v\<cdot>y \<and> (length x) = (nat m) \<and> (length v) = min (nat n) ((length w) - (nat m))" using  strict_factor_embedding zero_less_nat_eq by (metis add_diff_cancel_left' less_add_same_cancel1)
  thus ?thesis by auto
qed
  
  
  

theorem substr_correct2:
fixes m::"int" and n::"int"
shows "\<not>(0\<le>m \<and> m < (int (length w)) \<and> 0 < n) \<Longrightarrow> (str_substr w m n = \<epsilon>)"
  by auto
  

abbreviation str_prefixof:: "uc_string \<Rightarrow> uc_string \<Rightarrow> bool" where "str_prefixof \<equiv> prefix"
abbreviation str_suffixof:: "uc_string \<Rightarrow> uc_string \<Rightarrow> bool" where "str_suffixof \<equiv> suffix"

(* Correctness of prefixof: \<lbrakk>str.prefixof\<rbrakk>(v, w) = true iff w = vx₂ for some word x *)
theorem prefixof_correct: "str_prefixof v w \<longleftrightarrow> (EX x. w = v@x)"
  by (simp add: prefix_def)


(* Correctness of suffixof: \<lbrakk>str.suffixof\<rbrakk>(v, w) = true iff w = xv₂ for some word x *)
theorem suffix_correct: "str_suffixof v w \<longleftrightarrow> (EX x. w = x@v)"
  by (simp add: suffix_def) 

abbreviation str_contains:: "uc_string \<Rightarrow> uc_string \<Rightarrow> bool" where "str_contains \<equiv> Words.contains"

 

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
  fixes i::"nat"
  assumes "i\<ge>0" and "i \<le> length w" and "str_contains (drop  i w) v"
  shows "EX n. (str_indexof w v (int i)) = (int n) \<and> (EX x y. w = x@v@y \<and> n = (length x) \<and> i\<le>n \<and> (\<forall>n'. n' < n \<longrightarrow> (\<nexists>x' y'. (length x') = n' \<and> i\<le>n' \<and> w = x'@v@y')))"
proof -
  from assms have "\<exists>n. (str_indexof w v (int i)) = (int n)"  by (simp add: contains_iff_find_index option.case_eq_if zero_le_imp_eq_int)
  then have f1:"\<exists>n. find_index  (drop i w) v = Some n" using assms(3) contains_iff_find_index by blast
  then have f2:"\<exists>n. find_index  (drop i w) v = Some n \<and> (\<exists>x y. w = x@v@y \<and> (length x) = (n+i) \<and> (\<forall>x'. ((length x') < (n+i) \<and> (length x') \<ge> i) \<longrightarrow> (\<nexists>y'. w = x'@v@y')))"  using assms(2) find_index_of_suffix_returns_first by blast
  then show ?thesis  by (metis int_eq_iff int_ops(5) le_add2 option.simps(5))
qed
  
theorem indexof_correct2: 
   "(i < 0 \<or> \<not>(str_contains (drop (nat i) w) v)) \<Longrightarrow> (str_indexof w v i) = -1"
  using contains_iff_find_index by fastforce


abbreviation str_replace:: "uc_string \<Rightarrow> uc_string \<Rightarrow> uc_string \<Rightarrow> uc_string" where "str_replace \<equiv> replace"

theorem replace_correct1: "\<not>str_contains w v \<Longrightarrow> str_replace w v u = w" by (simp add: replace_id_if_not_contains)
theorem replace_correct2: "str_contains w v \<Longrightarrow> \<exists>x y. str_replace w v u = x@u@y \<and> w = x@v@y \<and> (\<forall> x'. (length x') < (length x) \<longrightarrow> (\<nexists>y'. w=x'@v@y'))"
  by(auto simp only: replace_first_factor)
  
  

(* Regular Expression Functions *)
type_synonym uc_regex = "196607 regex"
(*type_synonym uc_regex = "nat regex"*)

abbreviation str_in_re:: "uc_string \<Rightarrow> uc_regex \<Rightarrow> bool" where "str_in_re w R \<equiv> re_contains w R"

theorem in_re_correct:"str_in_re w R \<longleftrightarrow> w \<in> (lang R)"
  by (auto simp add: re_contains_def derivative_correctness)


abbreviation str_to_re:: "uc_string \<Rightarrow> uc_regex" where "str_to_re w \<equiv> regex.Const w"
theorem to_re_correct: "lang (str_to_re w) = {w}" by simp

abbreviation re_none:: "uc_regex" where "re_none \<equiv> regex.None"
theorem re_none_correct: "lang re_none = {}" by simp

abbreviation re_allchar:: "uc_regex" where "re_allchar \<equiv> regex.Any"
theorem re_allchar_correct: "lang re_allchar = {w. (length w) = 1}" by simp
  
(* missing:  re_all*)

abbreviation re_concat:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex"  where "re_concat \<equiv> RegEx.re_concat"
theorem re_concat_correct: "(lang (re_concat r e)) = {x@y|x y. x \<in> (lang r) \<and> y \<in> (lang e)}" 
  by (simp add: Regular.concat_def re_concat_correct)

abbreviation re_union:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where "re_union  \<equiv> RegEx.re_union"
theorem re_union_correct: "lang (re_union r e) = {w|w. w \<in> (lang r) \<or> w \<in> (lang e)}"
  by (simp add: Un_def re_union_correct)

abbreviation re_inter:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where "re_inter  \<equiv> RegEx.re_inter"
theorem re_inter_correct: "lang (re_inter r1 r2) = {w|w. w\<in> (lang r1) \<and> w \<in> (lang r2)}"
  by (auto simp add: re_inter_correct)
  

abbreviation re_star:: "uc_regex \<Rightarrow>uc_regex" where "re_star \<equiv> RegEx.re_star "
theorem re_star_correct: "((lang (re_star r)) = k) \<Longrightarrow> \<epsilon> \<in> k \<and> (concat (lang r) k) \<subseteq> k"
  using concat_star_subset re_star_correct by fastforce
  
abbreviation re_plus:: "uc_regex \<Rightarrow> uc_regex" where "re_plus r \<equiv> RegEx.re_plus r"
theorem re_plus_correct: "lang (re_plus r) = lang (re_concat r (re_star r))" by (simp add: re_plus_def)

(* missing: re_inter, re_com, re_diff,  re_pow, re_loop *)
fun re_range:: "uc_string \<Rightarrow> uc_string \<Rightarrow> uc_regex" where 
"re_range (l#\<epsilon>) (u#\<epsilon>) = RegEx.re_range l u"|
"re_range _ _ = RegEx.None"

theorem re_range_correct1: "(length l) = 1 \<and> (length u) = 1 \<Longrightarrow> (lang (re_range l u)) = {v#\<epsilon>|v ll uu. l=(ll#\<epsilon>) \<and> u = (uu#\<epsilon>) \<and> ll \<le> v \<and> v \<le> uu}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
  by (auto split: if_splits)

theorem re_range_correct2: "(length l) \<noteq> 1 \<or> (length u) \<noteq> 1 \<Longrightarrow> (lang (re_range l u)) = {}" 
  apply(cases \<open>(l, u)\<close> rule:re_range.cases)
  by (auto split: if_splits)
  
abbreviation re_opt::"uc_regex \<Rightarrow> uc_regex" where "re_opt r \<equiv> re_union (Const \<epsilon>) r"

abbreviation re_comp::"uc_regex \<Rightarrow> uc_regex" where "re_comp \<equiv> RegEx.re_comp"
theorem re_comp_correct: "lang (re_comp r) = UC - (lang r)"
  by (auto simp add: re_comp_correct UC_def)

abbreviation re_diff:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where "re_diff \<equiv> RegEx.re_diff"
theorem re_diff_correct: "lang (re_diff r1 r2) = (lang r1) - (lang r2)" 
  by (simp add: re_diff_correct)

abbreviation re_pow::"nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where "re_pow n r \<equiv> RegEx.re_pow r n"
theorem re_pow_correct1: "lang(re_pow 0 r) = {\<epsilon>}" by auto
theorem re_pow_correct2: "lang (re_pow (Suc n) r ) = concat (lang r) (lang (re_pow n r))"
  by (simp add: RegEx.re_concat_correct)

abbreviation re_loop:: "nat \<Rightarrow> nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where "re_loop a b r \<equiv> RegEx.re_loop r a b"
theorem re_loop_correct1: "a \<le> b \<Longrightarrow> lang (re_loop a b r) = (\<Union>x\<in>{a..b}. (lang (re_pow x r)))"
  apply(auto)
  using re_loop_iff1 apply (metis atLeastAtMost_iff)
  using re_loop_iff1  using le_trans by blast
theorem re_loop_correct2: "a > b \<Longrightarrow> lang (re_loop a b r) = {}"
  using re_loop_iff2 re_none_correct by metis

  

end