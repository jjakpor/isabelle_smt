theory Words      
  imports Main "HOL-Library.Sublist"
begin

no_notation Groups.times_class.times (infixl "*" 70)


type_synonym 'a word = "'a list"
abbreviation Epsilon::"'a word" ("\<epsilon>") where "Epsilon \<equiv> []" 




(* Basic Operations *)


primrec first:: "'a word \<Rightarrow> 'a word" where
"first \<epsilon> = \<epsilon>"|
"first (a#w) = a#\<epsilon>"

definition at:: "'a word \<Rightarrow> nat \<Rightarrow> 'a word" where "at w i \<equiv> first (drop i w)"



primrec concat_all:: "'a word list \<Rightarrow> 'a word"
  where
  "concat_all [] = Epsilon" |
  "concat_all (w#ws) = w@(concat_all ws)"




(* Basic substring relations *)

definition fac :: "'a word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a word" where "fac w s l = take l (drop s w)"
definition is_prefix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_prefix v w = ((take (size v) w) = v)"
definition is_suffix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_suffix v w = is_prefix (rev v) (rev w)"
definition is_not_prefix:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where "is_not_prefix v w = (\<not>is_prefix v w)"

lemma [simp]:"fac w 0 (size w) = w"
  unfolding fac_def
  apply(auto)
  done

lemma [simp]: "fac Epsilon s l = Epsilon"
  unfolding fac_def
  apply(auto)
  done

lemma [simp]: "length (fac w s 0) = 0"
  apply(auto simp add: fac_def)
  done


lemma prefix_not_shorter[simp]:"(length w) < (length v) \<Longrightarrow> \<not>(is_prefix v w)"
  apply(auto simp add: is_prefix_def)
  done

lemma suffix_not_shorter[simp]:"(length w) < (length v) \<Longrightarrow> \<not>(is_suffix v w)"
  apply(auto simp add: is_suffix_def)
  done


lemma factor_embedding:"fac w s l = u \<Longrightarrow> EX x y. x@u@y = w"
  unfolding fac_def  
  apply (metis append_take_drop_id)
  done

lemma factorization:"w = x@u@y \<Longrightarrow> EX s l. fac w s l = u"
  unfolding fac_def  
  apply (metis append_eq_conv_conj)
  done

lemma factor_size_bound:"w = x@v@y \<Longrightarrow> (length v) \<le> (length w)"
  by auto

lemma prefix_iff_startswith: "is_prefix u w \<longleftrightarrow> (EX r. w = u@r)"
  apply(auto simp add: is_prefix_def)
  by (metis append_take_drop_id)

lemma prefix_refl[simp]:"is_prefix w w" by (auto simp add: is_prefix_def)

lemma suffix_iff_endswith: "is_suffix u w \<longleftrightarrow> (EX r. w = r@u)"
  apply(auto simp add: is_prefix_def is_suffix_def)
  by (metis append_take_drop_id rev_append rev_rev_ident)

lemma suffix_refl[simp]:"is_suffix w w" by (auto simp add: is_suffix_def)


primrec contains:: "'a word \<Rightarrow> 'a word \<Rightarrow> bool" where
"contains \<epsilon> v = (v = \<epsilon>)" |
"contains (x#u) v = ((is_prefix v (x#u)) \<or> (contains u v))" 

lemma contains_iff_fac: "contains w v \<longleftrightarrow> (EX x y. w = x@v@y)"
  apply(induct w)
   apply(auto simp add: prefix_iff_startswith is_prefix_def)+
   apply (metis append_Cons)
  by (metis append_eq_Cons_conv)


lemma not_contains_no_fac_has_prefix:"(\<not>contains w d) \<Longrightarrow> w = x@y \<Longrightarrow> (\<not> is_prefix d y)"
  apply(auto simp add: contains_iff_fac)
  by (metis prefix_iff_startswith)

lemma if_contains_then_fac_has_prefix:"(contains w d) \<Longrightarrow> EX x y. w = x@y \<and> (is_prefix d y)"
  apply(auto simp add: contains_iff_fac)
  using prefix_iff_startswith by blast

lemma epsilon_contains_epsilon: "contains \<epsilon> v \<Longrightarrow> v = \<epsilon>"
  by auto

primrec suc_opt:: "nat option \<Rightarrow> nat option" where
"suc_opt (Some r) = (Some (Suc r))" |
"suc_opt None = None"

primrec find:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
"find \<epsilon> v = (if (v = \<epsilon>) then Some 0 else None)"|
"find (a#w) v = (if (is_prefix v (a#w)) then Some 0 else suc_opt (find w v))"


lemma find_iff_contains: "contains w v \<longleftrightarrow> (EX r. find w v = Some r)"
  apply(induct w)
   apply(auto)
  done

lemma find_epsilon: "find w \<epsilon> = Some 0"
  apply(induct w)
   apply(auto)
  apply(auto simp add: is_prefix_def)
  done

lemma find_in_epsilon[simp]: "find \<epsilon> w = (if w = \<epsilon> then Some 0 else None)"
  by auto

lemma find_if_prefix:"find w v = Some 0 \<Longrightarrow> is_prefix v w"
  apply(auto simp add:is_prefix_def)
  apply(cases w)
   apply (metis contains.simps(1) find_iff_contains take_Nil)
  apply(auto)
  by (metis is_prefix_def nat.distinct(1) not_Some_eq option.inject suc_opt.simps(1) suc_opt.simps(2))

lemma prefix_shorter:"is_prefix v w \<Longrightarrow> (length v) \<le> (length w)"
  using linorder_le_less_linear prefix_not_shorter by auto


lemma find_finds_factor:"find w v = Some r \<Longrightarrow> EX x y. w = x@v@y"
  apply(induct w)
   apply(auto split: if_splits simp add: is_prefix_def)
   apply (metis append_Nil append_take_drop_id)
  by (metis Words.find.simps(2) contains_iff_fac find_iff_contains)


lemma find_finds_factor2:"find w v = Some r \<Longrightarrow> EX x y. w = x@v@y \<and> r = (length x)"
  apply(induct w)
   apply(auto split: if_splits simp add: is_prefix_def)
   apply (metis append_take_drop_id)
  sorry


lemma suffixes_set:"x \<in> set (suffixes w) \<Longrightarrow> is_suffix x w"
  apply(auto simp add: suffix_iff_endswith)
  using suffix_def by blast

definition suffix_with_prefix::"'a word \<Rightarrow> 'a word \<Rightarrow> 'a word option" where
"suffix_with_prefix w v = List.find (is_prefix v) (suffixes w)" 



primrec find_subword_acc:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat \<Rightarrow> nat option" where
"find_subword_acc \<epsilon> s acc = (if s = \<epsilon> then Some acc else None)"|
"find_subword_acc (a#w) s acc = (if (is_prefix s (a#w)) then Some acc else (find_subword_acc w s (Suc acc)))"


value "find_subword_acc ''abc'' ''b'' 0"

  
definition find_subword:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
"find_subword w v = find_subword_acc w v 0"


lemma find_epsi_in_epsi[simp]:"find_subword \<epsilon> \<epsilon> = Some 0"
  by (auto simp add: find_subword_def  split: if_splits)


lemma find_subword_in_epsi[simp]:"find_subword \<epsilon> v = Some r \<Longrightarrow> v = \<epsilon>"
  by (auto simp add: find_subword_def  split: if_splits)

lemma find_epsi_in_word[simp]:"find_subword w \<epsilon> = Some 0"
  apply(cases w)
   apply simp
  by (simp add: find_subword_def is_prefix_def)


lemma "find_subword w v = Some r \<Longrightarrow> is_prefix v (drop r w)"
   unfolding find_subword_def
  apply(induct w)
    apply(auto simp add: is_prefix_def)
    apply (metis option.simps(3))
   apply(auto split: if_splits)
   sorry



value "rev (enumerate 0 (suffixes ''abc''))"

lemma "(l, s) \<in> (set (enumerate 0 (suffixes w))) \<Longrightarrow> l = (length s)"
  apply(induct w)
   apply force
  apply(auto simp add:  enumerate_append_eq)
 done


definition find_s:: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word option" where
"find_s w v = List.find (is_prefix v) (suffixes w)"


lemma suffix_append_right: "is_suffix v w \<Longrightarrow> is_suffix (v@x) (w@x)"
  by (simp add: suffix_iff_endswith)


lemma find_is_suffix:"find_s w v = Some s \<Longrightarrow> is_prefix v s"
  apply(cases w)
  apply(auto simp add: find_s_def split: if_splits)
   apply (simp add: is_prefix_def)
  by (metis find_Some_iff is_prefix_def)

lemma find_finds_prefix:"find_s w v = Some s \<Longrightarrow> is_suffix s w"
  apply(auto simp add: find_s_def is_suffix_def is_prefix_def)
  by (metis find_Some_iff is_prefix_def is_suffix_def length_rev nth_mem suffixes_set)

lemma "w = x@s \<and> s = v@y \<Longrightarrow> w = x@v@y" by auto

lemma find_finds_factor3:"find_s w v = Some s \<Longrightarrow> EX x y. w = x@v@y"
  by (metis find_finds_prefix find_is_suffix prefix_iff_startswith suffix_iff_endswith)

lemma aux2:"find_s w v = Some s \<Longrightarrow> EX x. w = x@s"
  by (metis find_finds_prefix suffix_iff_endswith)

lemma aux3: "w = x@s \<Longrightarrow> (length x) = (length w) - (length s)" by auto

lemma aux4:"find_s w v = Some s \<Longrightarrow> EX x y. w = x@v@y \<and> (length x) = (length w)-(length s)"
  by (metis aux2 aux3 find_is_suffix prefix_iff_startswith)

definition find_index:: "'a word \<Rightarrow> 'a word \<Rightarrow> nat option" where
"find_index w v = (case find_s w v of Some r \<Rightarrow>  Some ((length w) - (length r)) | None \<Rightarrow> None)"

lemma find_finds_factor4:"find_index w v = Some r \<Longrightarrow> EX x y. w = x@v@y"
  unfolding find_index_def
  by (metis find_finds_factor3 not_Some_eq option.simps(4))


lemma find_finds_factor5:"find_index w v = Some r \<Longrightarrow> EX x y. w = x@v@y \<and> (length x) = r"
  unfolding find_index_def
  by (metis (no_types, lifting) aux4 option.case_eq_if option.collapse option.distinct(1) option.sel)

lemma find_finds_factor6:"find_index w v = Some r \<Longrightarrow> EX x y. w = x@v@y \<and> (length x) = r \<and> (\<forall> rr xx yy. rr<r \<longrightarrow> (length x) = rr \<longrightarrow> )"
  unfolding find_index_def
  by (metis (no_types, lifting) aux4 option.case_eq_if option.collapse option.distinct(1) option.sel)

end





