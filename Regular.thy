theory Regular      
  imports Words
begin

(* Regular Languages *) 
type_synonym 'a RegLang = "'a word set"

(* Regular Operations *)
definition concat :: "'a RegLang \<Rightarrow> 'a RegLang \<Rightarrow> 'a RegLang" where "concat R S = {u*v |u v. u:R & v:S}"

lemma concat_containment1: "a \<in> A \<and> b \<in> B \<Longrightarrow> (a * b) \<in> (concat A B)"
  apply(auto simp add: concat_def)
  done

lemma concat_containment2: "w \<in> (concat A B) \<Longrightarrow> \<exists>a b. w = a*b \<and> a \<in> A \<and> b \<in> B "
  apply(auto simp add: concat_def)
  done

lemma epsilon_concat_iff: "Epsilon \<in> A \<and> Epsilon \<in> B \<longleftrightarrow> Epsilon \<in> (concat A B)"
  apply(auto simp add: concat_def)
  done

lemma epsilon_in_const_iff: "Epsilon \<in> {x} \<longleftrightarrow> x = Epsilon"
   apply(auto)
  done

primrec pow:: "'a RegLang \<Rightarrow> nat \<Rightarrow> 'a RegLang" 
  where
   "pow s 0 = {Epsilon}"|
   "pow s (Suc n) = concat s (pow s n)"

definition star :: "'a RegLang \<Rightarrow> 'a RegLang" where "star R = (\<Union>n. (pow R n))"

lemma epsilon_in_star[simp]: "Epsilon \<in> star R"
  apply(auto simp add: star_def)
proof -
  have "Epsilon \<in> pow R 0" by simp
  then show "EX n. Epsilon \<in> pow R n" by (rule exI)
qed

lemma epsilon_in_pow:"\<exists>n. Epsilon \<in> pow r n"
proof -
  have "Epsilon \<in> pow r 0" by simp
  thus ?thesis by (rule exI)
qed

lemma star_all_pows:"star r = {w|w n. w \<in> pow r n}"
  apply(auto simp add: star_def)
  done

lemma pow_not_zero:"n>0 \<and> w \<in> pow r n \<Longrightarrow> \<exists>m. w \<in> pow r (Suc m)"
  apply(induct n)
   apply(auto simp add: concat_def)
  done

lemma concat_star_subset: "w \<in> concat R (star R) \<Longrightarrow> w \<in> (star R)"
proof -
  assume "w \<in> concat R (star R)"
  then have "w \<in> {w |w n. w \<in> pow R (Suc n)}"  by (auto simp add: concat_def star_all_pows)
  then have "w \<in> {w |w m. w \<in> pow R m}" by fastforce
  then show "w \<in> (star R)" by (simp only: star_all_pows)
qed


lemma concat_star:"set ws \<subseteq> R \<Longrightarrow> concatn ws \<in> (star R)"
proof (induct ws)
  case Nil
  then show ?case by simp
next
  case IH:(Cons w ws)
  then have "w \<in> R \<and> concatn ws \<in> star R" by (simp add: IH) 
  then have "concatn (w#ws) \<in> concat R (star R)" by (auto simp add: concat_def Words.concat_def)
  then have "concatn (w#ws) \<in> (star R)" by (simp only: concat_star_subset)
  then show ?case by auto
qed


lemma star_remove_epsilons:"set ws \<subseteq> R \<Longrightarrow> \<exists>wsa. concatn ws = concatn wsa \<and> set wsa \<subseteq> R - {Epsilon}" (is "?P \<Longrightarrow> \<exists> vs. ?Q vs")
proof
  let ?vs = "filter (%u. u \<noteq> Epsilon) ws"
  show "?P \<Longrightarrow> ?Q ?vs" by (induct ws) auto  
qed

lemma x:"w \<in> pow r n \<Longrightarrow> \<exists>ws. w = concatn ws \<and> set ws \<subseteq> r"
proof (induct n arbitrary: r  w)
  case 0
  then show ?case by (metis Regular.pow.simps(1) concatn.simps(1) empty_subsetI list.set(1) singletonD)
next
  case IH:(Suc n)
  then have "w \<in> concat r (pow r n)" by simp
  then have "\<exists>x y. w = x*y \<and> x \<in> r \<and> y \<in> (pow r n)" by (force simp add: concat_def)
  then have "\<exists>x y. w = x*y \<and> (\<exists>ws. y = concatn ws \<and> set ws \<subseteq> r)" using IH by fastforce
  then have "\<exists>ws. w = concatn ws \<and> set ws \<subseteq> r" by (metis IH.hyps \<open>\<exists>x y. w = x * y \<and> x \<in> r \<and> y \<in> pow r n\<close> concatn.simps(2) insert_subset list.set(2))
  then show ?case by simp
qed


lemma star_is_concats: "star R = {concatn ws|ws. set ws \<subseteq> R}"
  unfolding star_all_pows
  apply(auto simp add: x)
  apply (metis UN_E concat_star star_def)
  done


lemma star_rm_epsilon: "star (R-{Epsilon}) = star R"
  unfolding star_is_concats
  apply(auto simp add: star_remove_epsilons)
  done

lemma [simp]:"w \<in> pow R n \<Longrightarrow> w \<in> (star R)"
  apply(auto simp add: star_def)
  done


(* Derivative of regular languages *)
definition deriv:: "'a \<Rightarrow> 'a RegLang \<Rightarrow> 'a RegLang" where  "deriv a R = {v |v. (a . v) \<in> R}" 

primrec derivw:: "'a word \<Rightarrow> 'a RegLang \<Rightarrow> 'a RegLang" where
  "derivw Epsilon R = R" |
  "derivw (a . w) R = derivw w (deriv a R)"

definition null:: "'a RegLang \<Rightarrow> 'a RegLang" where "(null L) = (if Epsilon \<in> L then {Epsilon} else {})"

lemma deriv_empty[simp]:"deriv a {} = {}"
  apply(simp add: deriv_def)
  done
 
lemma deriv_const[simp]:"deriv a {(b . w)} = (if a = b then {w} else {})"
  apply(auto simp add: deriv_def)
  done

lemma deriv_union[simp]: "deriv a (l1 \<union> l2) = (deriv a l1) \<union> (deriv a l2)"
  apply(auto simp add: deriv_def)
  done

lemma deriv_concat[simp]:"deriv a (concat L R) = (concat (deriv a L) R) \<union> (concat (null L) (deriv a R))"
  unfolding deriv_def concat_def null_def
  apply(auto simp add: eq_prefix_equals)
  done

lemma pow_not_epsilon_is_succ:"n>0 \<and> w \<in> pow R n \<Longrightarrow> \<exists>m. w \<in> pow R (Suc m)"
  apply(induct n)
   apply(auto simp add: pow_def)
  done

lemma star_unroll:"star r = (concat r (star r)) \<union> {Epsilon}"
proof -
  have "{w|w n. w \<in> pow r n} = {w |w n. (n>0 \<or> n=0) \<and> (w \<in> pow r n)}" by auto
  also have "... = {w |w n. (n>0 \<and> (w \<in> pow r n)) \<or> (n = 0 \<and> w \<in> pow r n) }" by auto
  also have "... = {w |w n. (n>0 \<and> (w \<in> pow r n))} \<union> {w |w n. (n = 0 \<and> w \<in> pow r n)}" by (auto simp only: Un_iff)
  also have "... = {w |w n. (n>0 \<and> (w \<in> pow r n))} \<union> {w |w n.  w \<in> pow r 0}" by simp
  finally have "{w|w n. w \<in> pow r n} = {w|w n. n>0 \<and> w \<in> pow r n} \<union> {w|w n. w \<in> pow r 0}" by auto
  then have "{w|w n. w \<in> pow r n} = {w|w n. 0<n \<and> w \<in> pow r n} \<union> (pow r 0)" by auto
  then have "{w|w n. w \<in> pow r n} = {w|w n. (\<exists>m. w \<in> pow r (Suc m))} \<union> (pow r 0)" by (force simp only: pow_not_zero)
  then have "{w|w n. w \<in> pow r n} = {w|w n m. w \<in> pow r (Suc m)} \<union> (pow r 0)" by (auto)
  then have "{w|w n. w \<in> pow r n} = {w|w n. w \<in> pow r (Suc n)} \<union> (pow r 0)" by (auto)
  then have "{w|w n. w \<in> pow r n} = {w|w n. w \<in> concat r (pow r n)} \<union> {Epsilon}" by (auto)
  then have "{w|w n. w \<in> pow r n} = {w|w n. w \<in> concat r (pow r n)} \<union> {Epsilon}" by (auto)
  then have "{w|w n. w \<in> pow r n} = {w|w n x y. w=x*y \<and> x \<in> r \<and> y \<in> (pow r n)} \<union> {Epsilon}" by (auto simp add: concat_def)
  then have "{w|w n. w \<in> pow r n} = {x*y|w n x y. x \<in> r \<and> y \<in> (pow r n)} \<union> {Epsilon}" by (auto simp add: concat_def)
  then have "{w|w n. w \<in> pow r n} = {x*y|x y. x \<in> r \<and> (\<exists>n. y \<in> (pow r n))} \<union> {Epsilon}" by (auto)
  then have "{w|w n. w \<in> pow r n} = {x*y|x y. x \<in> r \<and> (y \<in> {k |k n. k \<in> (pow r n)})} \<union> {Epsilon}" by (fastforce)
  then have "{w|w n. w \<in> pow r n} = (concat r {w|w n. w \<in> (pow r n)}) \<union> {Epsilon}" by (auto simp only: concat_def)
  then have "{w|w n. w \<in> pow r n} = (concat r (star r)) \<union> {Epsilon}" by (auto simp only: star_all_pows)
  then have "star r = (concat r (star r)) \<union> {Epsilon}" by (auto simp only: star_all_pows)
  then show ?thesis by simp
qed



lemma deriv_star[simp]:"deriv a (star R) = concat (deriv a R) (star R)"
proof -
  have "deriv a (star R) = deriv a (star (R-{Epsilon}))" by (auto simp only: star_rm_epsilon)
  also have "... = deriv a ((concat (R-{Epsilon}) (star (R-{Epsilon}))) \<union> {Epsilon})" by (metis star_unroll)
  also have "... = (deriv a (concat (R-{Epsilon}) (star (R-{Epsilon})))) \<union> (deriv a {Epsilon})" by (simp only: deriv_union)
  also have "... = deriv a (concat (R-{Epsilon}) (star (R-{Epsilon})))" by (simp add: deriv_def)
  also have "... = (concat (deriv a (R-{Epsilon})) (star (R-{Epsilon}))) \<union> (concat (null (R-{Epsilon})) (deriv a (star (R-{Epsilon}))))" by simp
  also have "... = (concat (deriv a (R-{Epsilon})) (star (R-{Epsilon}))) \<union> (concat {} (deriv a (star (R-{Epsilon}))))" by (auto simp add: null_def)
  also have "... =  (concat (deriv a (R-{Epsilon})) (star (R-{Epsilon})))" by (simp add: concat_def)
  also have "... = (concat (deriv a R) (star (R-{Epsilon})))" by (simp add: deriv_def)
  also have "... = (concat (deriv a R) (star R))" by (simp only: star_rm_epsilon)
  finally have "deriv a (star R) = concat (deriv a R) (star R)" by simp
  then show ?thesis by simp
qed


theorem deriv_correct:"w \<in> deriv a R \<longleftrightarrow> (a . w) \<in> R"
  apply(auto simp add: deriv_def)
  done





end