exec 2>&1
echo "module crypto-agda where" >$3
git ls-files . |
  grep -v experimental |
  grep -v '^crypto-agda.agda$' |
  grep '\.agda$' |
  sed -e 's|\(.*\)\.agda|import \1|' |
  tr / . >>$3
