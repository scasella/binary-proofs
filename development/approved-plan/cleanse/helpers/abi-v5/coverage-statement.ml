let abi_cleanse_registered_decode_qualified_statement =
 `!pc off s.
    bytes_loaded s (word pc) openssl_cleanse_mc /\
    read RIP (s:x86state) = word(pc+off) /\
    MEM off [0;4;7;11;13;17;19;21;25;29;31;48;55;57;59;63;67;69;72;76;83;87;89;93;95]
    ==> abi_all_decodes_cleanse_scalar s`;;
