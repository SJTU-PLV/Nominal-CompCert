for ((i=1;i<=$1;i++))
do
lemma='Lemma list_length'$i'_destruct: forall A (l:list A),
    length l = '$i' ->
    exists '
eles=''
lst='['

ltac='  |[H: length ?l = '$i', l: list _ |- _ ] =>
     generalize (list_length'$i'_destruct _ l H);'
    #  intros (? & ? & ?);subst;try clear H
intros='intros ('

for ((j=1;j<=$i;j++))
do
    eles="$eles b$j"
    intros="$intros""? & "
    if (($j==$i))
    then 
        lst="$lst""b$j"
    else
        lst="$lst""b$j;"
    fi
done

lst="$lst]"
intros="$intros""?);subst l;try clear H"

lemma=$lemma$eles', l='$lst'.
Proof.
  intros.
  destr_all_lists. repeat eexists.
Qed.'

ltac=$ltac"
    $intros"

echo "$lemma"
# echo "$ltac"
done