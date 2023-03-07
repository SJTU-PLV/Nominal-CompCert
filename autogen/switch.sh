if test "$1" = "riscv"
then
mv EncDecRet.v EncDecRet.v.$1;
mv VerificationCondition.v VerificationCondition.v.$1;
mv EncDecRet.v.x86 EncDecRet.v;
mv VerificationCondition.v.x86 VerificationCondition.v;
else
mv EncDecRet.v EncDecRet.v.$1;
mv VerificationCondition.v VerificationCondition.v.$1;
mv EncDecRet.v.riscv EncDecRet.v;
mv VerificationCondition.v.riscv VerificationCondition.v;
fi

rm *.vo