let cleanse_access_large_decomposition_statement =
 `!v n. 15<=n ==>
    let a=(8-v MOD 8) MOD 8 in
    let k=(n-a) DIV 8 in let r=(n-a) MOD 8 in
    a<8 /\ a<n /\ 0<k /\ r<8 /\ n=a+8*k+r /\
    (v+a) MOD 8=0 /\ (!i. i<a ==> ~((v+i) MOD 8=0))`;;
