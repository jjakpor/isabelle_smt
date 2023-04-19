theory Strings
  imports Core "strings/RegEx" "strings/Words"  "HOL-Library.Numeral_Type"  "HOL-Library.List_Lexorder"
begin

no_notation List.length ("\<bar>_\<bar>")
no_notation Groups.abs_class.abs  ("\<bar>_\<bar>")


section "Standard model for the SMT-LIB Theory of String"

subsection "Definition of Unicode characters"

text "The standard defines two sorts, String and RegLan. 
In the standard model, the domain of these sorts are fixed as the set of all words over the 
alphabet of unicode code points from 0 to 196606, and the powerset of this set, respectively.
We define the set of unicode code points as the ring of integers up to 196606.
Words as lists over this alphabet (type) and regular languages as regular expression over the
alphabet, equipped with a function that maps expression to actual languages."

type_synonym uc_char = "196607"
type_synonym uc_word = "uc_char word"
type_synonym uc_regex = "uc_char regex"

definition UC:: "uc_word set" where "UC = {w. True}"


subsection "Interpretation of the SMT-LIB theory of strings symbols"

text "In the following, we interprete all symbols of the SMT-LIB theory of strings.
The interprations are based on primitive functions implemented on lists and regular expressions.
Note that the symbols are not identicaly to the one state in the SMT-LIB theory due to syntactic
restrictions of Isabelle/HOL. However, there is a one to one mapping between the symbols used here
and the symbols used in SMT-LIB. This mapping is specified in 'spec.json'."


abbreviation str_char:: "uc_char \<Rightarrow> uc_word" where
  "str_char a \<equiv> a#\<epsilon>"

abbreviation str_concat:: "uc_word \<Rightarrow> uc_word  \<Rightarrow> uc_word" where 
  "(str_concat) u v \<equiv> u\<cdot>v" 

abbreviation str_len:: "uc_word \<Rightarrow> int" ("\<bar>_\<bar>") where  
  "str_len w \<equiv> of_nat (length w)"

abbreviation str_at:: "uc_word \<Rightarrow> int \<Rightarrow> uc_word" where 
  "str_at w i \<equiv> if i \<ge> 0 then w[(nat i); (nat i+1)] else \<epsilon>"

abbreviation str_substr:: "uc_word \<Rightarrow> int \<Rightarrow> int \<Rightarrow> uc_word" where 
  "str_substr w m n \<equiv> if (n \<ge> 0 \<and> 0\<le>m \<and> ((nat m) \<le> (length w)-1)) then  w[(nat m);(nat (m+n))] else \<epsilon>"

abbreviation str_prefixof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_prefixof \<equiv> prefix"

abbreviation str_suffixof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_suffixof \<equiv> suffix"

abbreviation str_contains:: "uc_word \<Rightarrow> uc_word \<Rightarrow> bool" where 
  "str_contains \<equiv> Words.contains"


(*fun str_indexof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> int \<Rightarrow> int" where 
  "str_indexof w v i = (if i \<ge> 0 \<and> (str_contains (str_substr w i \<bar>w\<bar>) v) \<and> i\<le>\<bar>w\<bar> then Int.int (str_indexof_nat w v (Int.nat i)) else -1)"*)

abbreviation str_indexof:: "uc_word \<Rightarrow> uc_word \<Rightarrow> int \<Rightarrow> int" where 
  "str_indexof w v i \<equiv> (if i\<ge>0 \<and>  (str_contains (str_substr w i \<bar>w\<bar>) v) \<and> i\<le>\<bar>w\<bar> then Int.int (indexof_nat w v (Int.nat i)) else -1)"

abbreviation str_replace:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace \<equiv> replace"

abbreviation str_replace_all:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace_all \<equiv> undefined"

abbreviation str_replace_re:: "uc_word \<Rightarrow> uc_regex \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace_re \<equiv> undefined"

abbreviation str_replace_re_all:: "uc_word \<Rightarrow> uc_regex \<Rightarrow> uc_word \<Rightarrow> uc_word" where 
  "str_replace_re_all \<equiv> undefined"

abbreviation str_in_re:: "uc_word \<Rightarrow> uc_regex \<Rightarrow> bool" where 
  "str_in_re w r \<equiv> nullable (rderivw w r)"

abbreviation str_to_re:: "uc_word \<Rightarrow> uc_regex" where 
  "str_to_re w \<equiv> regex.Const w"

abbreviation re_none:: "uc_regex" where 
  "re_none \<equiv> regex.None"

abbreviation re_allchar:: "uc_regex" where 
  "re_allchar \<equiv> regex.Any"

abbreviation re_all::"uc_regex" where
"re_all \<equiv> re_star re_allchar"

abbreviation re_concat:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_concat \<equiv> RegEx.re_concat"

abbreviation re_union:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_union  \<equiv> RegEx.re_union"

abbreviation re_inter:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_inter  \<equiv> RegEx.re_inter"

abbreviation re_star:: "uc_regex \<Rightarrow>uc_regex" where 
  "re_star \<equiv> RegEx.re_star"

abbreviation re_plus:: "uc_regex \<Rightarrow> uc_regex" where 
  "re_plus r \<equiv> RegEx.re_plus r"

fun re_range:: "uc_word \<Rightarrow> uc_word \<Rightarrow> uc_regex" where 
  "re_range (l#\<epsilon>) (u#\<epsilon>) = RegEx.re_range l u"|
  "re_range _ _ = RegEx.None"

abbreviation re_opt::"uc_regex \<Rightarrow> uc_regex" where 
  "re_opt r \<equiv> re_union (Const \<epsilon>) r"

abbreviation re_comp::"uc_regex \<Rightarrow> uc_regex" where
  "re_comp \<equiv> RegEx.re_comp"

abbreviation re_diff:: "uc_regex \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_diff \<equiv> RegEx.re_diff"

abbreviation re_pow::"nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where
  "re_pow n r \<equiv> RegEx.re_pow r n"

abbreviation re_loop:: "nat \<Rightarrow> nat \<Rightarrow> uc_regex \<Rightarrow> uc_regex" where 
  "re_loop a b r \<equiv> RegEx.re_loop r a b"


subsection "Model Proofs"

text "We shows that our interpretation of the functions satisfy all conditions stated by the SMT-LIB theory 
of strings, which thus proofs it to be equivalent to the standard model of the theory."

abbreviation smallest_set where
  "smallest_set K P \<equiv> P K \<and> (\<forall>K'. P K' \<longrightarrow> K \<subseteq> K')"

abbreviation smallest_int where
  "smallest_int n P \<equiv> P n \<and> (\<forall>n'. P n' \<longrightarrow> n \<le> n')"

abbreviation shortest_word where
  "shortest_word w P \<equiv> P w \<and> (\<forall>w'. P w' \<longrightarrow> \<bar>w\<bar> \<le> \<bar>w'\<bar>)"

theorem "UNIV = UC"  
  by (simp add: UC_def)

subsubsection "Lexicographic order"

theorem lexord_strict:"v < w \<longleftrightarrow> (v, w) \<in> lexord {(a, b). a<b}" 
  by (simp add: list_less_def)

theorem lexord:"v \<le> w \<longleftrightarrow> (v, w) \<in> lexord {(a, b). a<b} \<or> v = w" 
  by (simp add: list_le_def list_less_def)

subsubsection "Length"

text "Some lemmas about string length used later on"

lemma length_ge_0: "\<bar>w\<bar> \<ge> 0" 
  by auto

lemma length_less_0: "\<not>\<bar>w\<bar> < 0" 
  by auto

lemma length_int_nat: "\<bar>w\<bar> = int (length w)" 
  by auto

lemma length_int_nat_le: "m \<ge> 0 \<Longrightarrow> m \<le> \<bar>w\<bar> \<longleftrightarrow> (nat m) \<le> (length w)"
  by auto

lemma length_int_nat_sub: "m \<ge> 0 \<Longrightarrow> m \<le> \<bar>w\<bar> \<Longrightarrow> int ((length w) - (nat m)) = (\<bar>w\<bar> - m)"
  by auto

lemma length_int_nat_min: "m \<ge> 0 \<Longrightarrow> n \<ge> 0 \<Longrightarrow> int (min (nat m) (nat n)) = min m n"
  by auto

lemma length_int_nat_sub_min:
  assumes "\<bar>w\<bar> \<ge> m"
    and "n \<ge> 0"
    and "m \<ge> 0"
  shows "int (min (nat n) ((length w)-nat m)) = (min n (\<bar>w\<bar>- m))"
  using assms by auto

lemma of_nat_nat_inv: "x \<ge> 0 \<Longrightarrow> of_nat (nat x) = x" 
  by auto


subsubsection "Substrings (str.at, str.substr)"

theorem str_at:"str_at w n = str_substr w n 1" 
  by (simp split: if_splits add: diff_nat_eq_if)

lemma substr_factor_equal:
  assumes "0 \<le> m"
    and "m < \<bar>w\<bar>"
    and "0 < n"
  shows "str_substr w m n = (w[nat m; nat m + nat n])"
  using assms diff_nat_eq_if by auto

theorem str_substr1:
  assumes "0 \<le> m" and "m < \<bar>w\<bar>" and "0 < n"
  shows "\<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w =  x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and>  \<bar>v\<bar> = min n (\<bar>w\<bar> - m))"
  proof -
  from assms have "nat m < (length w) \<and> nat m \<le> nat m + nat n" by auto
  then have "\<exists>!v. (w[nat m; nat m + nat n]) = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (length x) = nat m \<and>
               (length v) = min ((nat m + nat n)-nat m) ((length w)-nat m))" 
    using factorization by metis
  then have "\<exists>!v. (w[nat m; nat m + nat n]) = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    by (metis add_diff_cancel_left' assms(1) int_nat_eq)
  then have "\<exists>!v. str_substr w m n = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> (length v) = min (nat n) ((length w)-nat m))" 
    using assms substr_factor_equal by presburger
  then have "\<exists>!v. str_substr w m n = v \<and>
             (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = int (min (nat n) ((length w)-nat m)))" 
    by simp
  then have "\<exists>!v. str_substr w m n = v \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> \<bar>x\<bar> = m \<and> \<bar>v\<bar> = (min n (\<bar>w\<bar>- m)))" 
    using length_int_nat_sub_min assms by auto
  then show ?thesis 
    by blast
qed

theorem str_substr2:
  assumes "\<not>(0 \<le> m \<and> m <  \<bar>w\<bar> \<and> 0 < n)"
  shows "str_substr w m n = \<epsilon>"
proof -
  from assms have assm:"(0 > m \<or> m \<ge> \<bar>w\<bar> \<or> 0 \<ge> n)" (is "?A \<or> ?B \<or> ?C") by auto
  then show ?thesis  using assm by fastforce
qed


subsubsection "Factors (str.prefixof, str.suffixof, str.contains)"

theorem str_prefix: "str_prefixof v w \<longleftrightarrow> (\<exists>x. w = v\<cdot>x)"   by (simp add: prefix_def)

theorem str_suffix: "str_suffixof v w \<longleftrightarrow> (\<exists>x. w = x\<cdot>v)"   by (simp add: suffix_def)

theorem str_contains: "str_contains w v \<longleftrightarrow> (\<exists>x y. w = x\<cdot>v\<cdot>y)" 
  by (auto simp add: contains_iff_factor sublist_def)
  

subsubsection "Searching and replacing (str.indexof, str.replace variants)"


text "The SMT-LIB standard states the following theorems

str_contains v w \<Longrightarrow> \<exists>n. str_indexof w v i = n \<and> (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>) \<and> (\<forall>n'. n' < n \<longrightarrow> (\<exists>x' y'. w = x'\<cdot>v\<cdot>y' \<and> i \<le> n' \<and> n = \<bar>x'\<bar>)) and
\<not>str_contains v w \<Longrightarrow> str_indexof w v i = -1 and

However, they are inconsistent. We find counterexamples.

- if i\<le>\<bar>w\<bar> no such n exists 
  - Example: (indexof 'ab' \<epsilon> 3 = n) but no n wa and words x y satisfy 'ab' = x\<cdot>\<epsilon>\<cdot>y \<and> \<bar>x\<bar>=n \<and> n\<ge>3
- if (str_contains v w) but not str_contains (str_substr w i \<bar>w\<bar>) v, then no such n exists
  - Example: (indexof 'ab' 'a' 1 = n) but no n and words x y satisfy 'ab' = x\<cdot>'a'\<cdot>y \<and> \<bar>x\<bar> = n \<and> n\<ge>1

To be consistent, we need (str_contains (str_substr w i \<bar>w\<bar>) v)  instad of 
(str_contains v w), and additionally need the premise i\<le>\<bar>w\<bar>.
If either of these premises is not met, or i<0, the the function must evaluate to -1.
"

theorem str_indexof1:
  assumes "i\<ge>0" and "i\<le>\<bar>w\<bar>" and "str_contains (str_substr w i \<bar>w\<bar>) v"
  shows "\<exists>n. str_indexof w v i = n \<and> smallest_int n (\<lambda>n. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> i \<le> n \<and> n = \<bar>x\<bar>))" 
proof -
  have "nat i \<le> length w"
    using assms(2) nat_le_iff by blast
  moreover
  have "sublist v (drop (nat i) w)"
    by (smt (verit, best) assms(3) contains_iff_factor dual_order.refl factor.elims(1) 
        factor_suffix nat_add_distrib nat_int sublist_Nil_left sublist_Nil_right trans_le_add2)
  ultimately
  have "smallest_int (indexof_nat w v (Int.nat i)) (\<lambda>n. (\<exists>x y. w = x\<cdot>v\<cdot>y \<and> (Int.nat i) \<le> n \<and> n = length x))"
    using str_indexof_nat1[of "Int.nat i" w v] by auto
  then show ?thesis
    by (metis assms nat_int nat_le_iff)
qed

theorem str_indexof2: 
  assumes "i<0 \<or> i>\<bar>w\<bar> \<or> \<not> str_contains (str_substr w i \<bar>w\<bar>) v" 
  shows "str_indexof w v i = -1" 
proof -
  {
    assume "i<0"
    then have ?thesis
      by auto
  }
  moreover
  {
    assume "\<not> str_contains (str_substr w i \<bar>w\<bar>) v" 
    then have ?thesis
      using assms indexof_if_not_contains''' by presburger
  }
  moreover
  {
    assume "i>\<bar>w\<bar>"
    then have ?thesis
      using assms by auto 
  }
  ultimately show ?thesis 
    using assms by metis
qed

theorem str_replace1:
  assumes "str_contains w v"
  shows "\<exists>x y. str_replace w v u = x\<cdot>u\<cdot>y \<and> w = x\<cdot>v\<cdot>y \<and> (\<forall> x'. (\<exists>y'. w=x'\<cdot>v\<cdot>y') \<longrightarrow> \<bar>x\<bar> \<le> \<bar>x'\<bar>)"
  using replace_first_factor 
  by (metis assms of_nat_mono)


theorem str_replace2: 
  assumes "\<not> str_contains w v"
  shows "str_replace w v u = w" 
  sledgehammer
  using assms replace_id_if_not_contains by blast

(* TODO: Add replace_all, replace_re, replace_all_re! *)


subsubsection "Regular languages"

text "We represent regular languages using regular expression accompanied by a lang function that
maps expression to languages."

text "We first who that this lang operator maps into the powerset of all unicode strings"

theorem re_lang_unicode: "range (lang::(uc_char regex \<Rightarrow> uc_char word set)) \<subseteq> Pow UC"
  using UC_def by force

theorem str_to_re: "lang (str_to_re w) = {w}" by auto

theorem str_in_re: "str_in_re w R \<longleftrightarrow> w \<in> (lang R)" 
  by (auto simp add: derivw_nullable_contains contains_derivw_nullable)
  

paragraph "Regular Operators"

theorem re_none: "lang re_none = {}" by auto

theorem re_allchar: "lang re_allchar = {w. \<bar>w\<bar> = 1}" by auto

theorem re_all: "lang re_all = UC"
  using UC_def star_any_is_univ by auto

theorem re_concat: "lang (re_concat r e) = {x\<cdot>y|x y. x \<in> lang r \<and> y \<in> lang e}" 
  by (simp add: Regular.concat_def re_concat_correct)

theorem re_union: "lang (re_union r e) = {w|w. w \<in> lang r \<or> w \<in> lang e}" 
  by (simp add: Un_def re_union_correct)

theorem re_inter: "lang (re_inter r1 r2) = {w|w. w\<in> lang r1 \<and> w \<in> lang r2}" 
  by (auto simp add:  re_inter_correct)

lemma Star_smallest:
  assumes "w \<in> (pow (lang r) n)"
  assumes "\<epsilon> \<in> K'"
  assumes "{x \<cdot> y |x y. x \<in> lang r \<and> y \<in> K'} \<subseteq> K'"
  shows "w \<in> K'"
  using assms
proof (induction n arbitrary: w)
  case 0
  then show ?case
    by (simp add: star_all_pows star_of_empty)
next
  case (Suc n)
  from Suc(2) have "\<exists>u v. w = u \<cdot> v \<and> u \<in> (lang r) \<and> v \<in> pow (lang r) n"
    by (simp add: Regular.concat_def)
  then obtain u v where u_v_p: "w = u \<cdot> v" "u \<in> lang r" "v \<in> pow (lang r) n"
    by auto
  then have "v \<in> K'"
    using Suc(1)[of v] Suc(3) Suc(4) by auto
  then show ?case
    using u_v_p Suc by auto
qed

abbreviation smallest where
  "smallest K P \<equiv> P K \<and> (\<forall>K'. P K' \<longrightarrow> K \<subseteq> K')"

theorem re_star: "smallest (lang (Star r)) (\<lambda>K. \<epsilon> \<in> K \<and> {x\<cdot>y | x y. x \<in> lang r \<and> y \<in> K} \<subseteq> K)"
proof -
  have "\<epsilon> \<in> lang (r\<^sup>\<star>)"
    by simp
  moreover
  have "{x \<cdot> y |x y. x \<in> lang r \<and> y \<in> lang (r\<^sup>\<star>)} \<subseteq> lang (r\<^sup>\<star>)"
    by (auto simp add: concat_containment re_star_correct star_subsumes)
  moreover
  have "(\<forall>K'. \<epsilon> \<in> K' \<and> {x \<cdot> y |x y. x \<in> lang r \<and> y \<in> K'} \<subseteq> K' \<longrightarrow> lang (r\<^sup>\<star>) \<subseteq> K')"
    using Star_smallest by (auto simp add: star_def)
  ultimately
  show ?thesis
    by auto
qed

theorem re_plus: "lang (re_plus r) = lang (re_concat r (re_star r))"  
  by auto

theorem re_range1: "\<bar>l\<bar> = 1 \<and> \<bar>u\<bar> = 1 \<Longrightarrow> lang (re_range l u) = {v| v. l \<le> v \<and>  v\<le>u \<and> \<bar>v\<bar> = 1}" 
 apply(cases \<open>(l, u)\<close> rule: re_range.cases)
      apply (auto split: if_splits)
   apply (metis (no_types, lifting) Cons_less_Cons length_0_conv length_Suc_conv linorder_not_le)
  by (meson Cons_le_Cons dual_order.trans)

theorem re_range2: "\<bar>l\<bar> \<noteq> 1 \<or> \<bar>u\<bar> \<noteq> 1 \<Longrightarrow> lang (re_range l u) = {}" 
  by (cases \<open>(l, u)\<close> rule:re_range.cases) (auto split: if_splits)

theorem re_comp: "lang (re_comp r) = UNIV - (lang r)"
  by (simp add: Compl_eq_Diff_UNIV re_comp_correct)

theorem re_diff: "lang (re_diff r1 r2) = lang r1 - lang r2" 
  by (simp add: re_diff_correct)

theorem re_pow1: "lang (re_pow 0 r) = {\<epsilon>}" 
  by auto

theorem re_pow2: "\<forall>n. re_pow (Suc n) r =  re_concat r (re_pow n r)" 
  by simp

theorem re_loop1: 
  assumes "a \<le> b"
  shows "lang (re_loop a b r) = (\<Union>x\<in>{a..b}. (lang (re_pow x r)))"
  using re_loop_iff1[of a b] using assms atLeastAtMost_iff by fastforce

theorem re_loop2: "a > b \<Longrightarrow> lang (re_loop a b r) = {}" 
  by (simp add: re_loop_None_if)

lemma "12::uc_char < 13::uc_char" 
  sorry

end