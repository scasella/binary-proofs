let cleanse_prefix_zero_store_bytes_statement =
 `!m p i k. read (bytes(p:int64,i)) m = 0
    ==> read (bytes(p,i+k))
          (write (bytes(word_add p (word i),k)) 0 m) = 0`;;
let cleanse_prefix_zero_store_bytes64_statement =
 `!m p i. read (bytes(p:int64,i)) m = 0
    ==> read (bytes(p,i+8))
          (write (bytes64(word_add p (word i))) (word 0:int64) m) = 0`;;
