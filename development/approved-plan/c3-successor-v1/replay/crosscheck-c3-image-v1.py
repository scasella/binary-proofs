#!/usr/bin/env python3
"""Trusted C3 ELF/GNU/formal-source correspondence crosscheck, not a proof.

Instantiation of C1's parser/section/segment/relocation checks. Two call edges
are discovered from the frozen final artifact, not imported C1 address facts.
"""
import hashlib,json,re,struct,types
from pathlib import Path
PARSER_SHA='6f35da09dea20999a64f5698618b369822c3eac60ebe7d6b161021206f163cff'
OWN='development/approved-plan/held-out-transfer-v1/c3'
def sha(data):return hashlib.sha256(data).hexdigest()
def compact(text):return re.sub(r'\s+','',text)
def require(value,message):
    if not value:raise ValueError(message)
def mod_definition_literals(source):
    rows=re.findall(r'let\s+(\w+)\s*=\s*new_definition\s*`([^`]*)`;;',source,re.S)
    require(len(rows)==len(dict(rows)), 'Duplicate C3 formal definition')
    return dict(rows)
def crosscheck(root,gnu_output):
    parser=root/'scripts/inventory.py'
    require(sha(parser.read_bytes())==PARSER_SHA,'Pinned ELF parser changed')
    mod=types.ModuleType('c3_fresh_pinned_elf');mod.__file__=str(parser)
    exec(compile(parser.read_bytes(),str(parser),'exec'),mod.__dict__)
    own=root/OWN; inventory=json.loads((own/'artifact/inventory-v1.json').read_text())
    require(inventory['schema']=='c3-final-linked-acquisition-v1','Wrong C3 artifact inventory')
    bias=inventory['load_bias'];elf=mod.ELF(own.parent/inventory['artifact'])
    require(elf.sha256==inventory['artifact_sha256'] and elf.type==3 and elf.machine==62,'C3 artifact/hash/ET_DYN/x86-64 mismatch')
    caller=inventory['caller']
    symbol,=[s for s in elf.symbols if s['table']=='.dynsym' and s['name']==caller['symbol']]
    entry=symbol['vaddr'];fileoffset,code=elf.extract(entry,symbol['size'])
    require(entry==caller['elf_vaddr'] and fileoffset==caller['file_offset'] and symbol['size']==caller['size'] and code.hex()==caller['bytes_hex'] and sha(code)==caller['bytes_sha256'],'Final caller symbol/offset/byte pin mismatch')
    require(bias+entry==caller['loaded_address'],'Declared caller address differs from load bias')
    rows=[]
    for line in (gnu_output/'disassembly.txt').read_text().splitlines():
        fields=line.split('\t')
        if len(fields)<3:continue
        m=re.fullmatch(r'\s*([0-9a-f]+):',fields[0])
        if not m:continue
        va=int(m[1],16)
        if not entry<=va<entry+len(code):continue
        raw=bytes.fromhex(fields[1]);mnemonic=fields[2].strip().split(None,1)[0]
        require(raw==code[va-entry:va-entry+len(raw)],'GNU disassembly bytes disagree with ELF')
        rows.append((va,raw,mnemonic))
    expected=[(r['elf_vaddr'],bytes.fromhex(r['bytes_hex']),r['mnemonic']) for r in caller['instructions']]
    require(rows==expected and sum(len(r[1]) for r in rows)==len(code),'GNU exact symbol instruction/byte coverage mismatch')
    readelf=(gnu_output/'readelf.txt').read_text()
    require('Advanced Micro Devices X86-64' in readelf and 'BIND_NOW' in readelf,'Fresh GNU machine/eager-binding mismatch')
    require(any(d['tag']==30 and d['value']&8 for d in elf.dynamic),'C3 missing DT_BIND_NOW')
    require(not any(r['type'] not in (6,7,8) for r in elf.relocations),'Unexpected relocation kind')
    links=[];plts=[]
    require({r['symbol'] for r in inventory['linkage']}=={'CRYPTO_memcmp','OPENSSL_cleanse'} and len(inventory['linkage'])==3,'Missing/duplicate supplier linkage')
    require({va for va,_,mn in rows if mn=='call'}=={r['call_elf_vaddr'] for r in inventory['linkage']},'Uninventoried/missing caller CALL')
    definitions=mod_definition_literals((own/'contract/definitions-v2.ml').read_text())
    raw_lists=[('c3_caller_mc',code)];got_reads=[];file_clauses=[];loaded_clauses=[];unique={} 
    file_clauses.append(f'(!i. i<{len(code)} ==> file_bytes(0x{entry:x}+i)=EL i c3_caller_mc)')
    loaded_clauses.append(f'bytes_loaded s (word 0x{bias+entry:x}) c3_caller_mc')
    for link in inventory['linkage']:
        call,=[r for r in rows if r[0]==link['call_elf_vaddr']]
        require(call[1][0]==0xe8 and len(call[1])==5,'Supplier transfer is not actual direct CALL encoding')
        continuation=call[0]+5;plt_va=continuation+struct.unpack_from('<i',call[1],1)[0]
        plt_file,plt=elf.extract(plt_va,16)
        require(plt[:2]==b'\xff\x25','Actual PLT prefix not RIP-relative indirect JMP')
        got_va=plt_va+6+struct.unpack_from('<i',plt,2)[0]
        require((continuation,plt_va,plt_file,got_va,plt.hex(),plt[:6].hex(),sha(plt[:6]))==(link['continuation_elf_vaddr'],link['plt_elf_vaddr'],link['plt_file_offset'],link['got_elf_vaddr'],link['plt_bytes_hex'],link['plt_prefix_hex'],link['plt_prefix_sha256']),'Actual CALL/PLT/GOT derivation mismatch')
        require((bias+call[0],bias+continuation,bias+plt_va,bias+got_va)==(link['call_loaded_address'],link['continuation_loaded_address'],link['plt_loaded_address'],link['got_loaded_address']),'Linkage loaded-address/load-bias mismatch')
        reloc,=[r for r in elf.relocations if r['offset']==got_va]
        symbol,=[s for s in elf.symbols if s['table']=='.dynsym' and s['name']==link['symbol']]
        require(reloc==link['relocation'] and reloc['type']==7 and reloc['symbol']==link['symbol'] and symbol['version']==link['symbol_version']=='OPENSSL_3.0.0','Supplier relocation/version mismatch')
        require(re.search(r'^0*'+f'{got_va:x}'+r'\s+\w+\s+R_X86_64_JUMP_SLOT\s+\w+\s+'+re.escape(link['symbol'])+r'@OPENSSL_3\.0\.0\s+\+\s+0\s*$',readelf,re.M),'Fresh GNU relocation/version mismatch')
        name='c3_crypto_plt_prefix' if link['symbol']=='CRYPTO_memcmp' else 'c3_cleanse_plt_prefix'
        signature=(plt_va,got_va,plt[:6],link['required_postinit_target'])
        if name in unique:
            require(unique[name]==signature,'Repeated supplier site has inconsistent PLT/GOT/target')
        else:
            unique[name]=signature
            raw_lists.append((name,plt[:6]));plts.append((plt_va,16))
            file_clauses.append(f'(!i. i<6 ==> file_bytes(0x{plt_va:x}+i)=EL i {name})')
            loaded_clauses.append(f'bytes_loaded s (word 0x{bias+plt_va:x}) {name}')
            got_reads.append(f'read (memory :> bytes64 (word 0x{bias+got_va:x})) s=word 0x{link["required_postinit_target"]:x}')
        links.append(dict(symbol=link['symbol'],actual_call_target=bias+plt_va,actual_got_slot=bias+got_va,declared_postinitialization_supplier_target=link['required_postinit_target'],continuation=bias+continuation))
    for r in elf.relocations:
        require(not any(r['offset']<a+n and a<r['offset']+8 for a,n in [(entry,len(code))]+plts),'Relocation overlaps proved instruction bytes')
    for name,raw in raw_lists:
        want=name+':byte list = ['+';'.join(f'word 0x{b:02x}' for b in raw)+']'
        require(compact(definitions[name])==compact(want),'Formal byte-list/final ELF mismatch: '+name)
    require(compact(definitions['c3_file_code'])==compact('c3_file_code (file_bytes:num->byte) <=> '+' /\\ '.join(file_clauses)),'Formal file-code extraction relationship mismatch')
    require(compact(definitions['c3_got'])==compact('c3_got (s:x86state) <=> '+' /\\ '.join(got_reads)),'Formal loaded GOT pointer mismatch')
    for fragment in loaded_clauses:
        require(compact(fragment) in compact(definitions['c3_loaded_code']),'Formal loaded caller/PLT bytes mismatch')
    def gnu_headers(kind):
        parsed=[]
        for line in readelf.splitlines():
            f=line.split()
            if not f or f[0]!=kind:continue
            parsed.append(dict(file_offset=int(f[1],16),vaddr=int(f[2],16),paddr=int(f[3],16),file_size=int(f[4],16),memory_size=int(f[5],16),align=int(f[-1],16),flags=sum(n for c,n in [('R',4),('W',2),('E',1)] if c in ''.join(f[6:-1]))))
        return parsed
    for label,kind in [('LOAD',1),('GNU_RELRO',0x6474e552)]:
        expected=[{k:p[k] for k in ['file_offset','vaddr','paddr','file_size','memory_size','align','flags']} for p in elf.ph if p['type']==kind]
        require(gnu_headers(label)==expected,'Fresh GNU/independent ELF image-header mismatch: '+label)
    sections={}
    for section in ['.text','.plt']:
        actual=elf.bytes(elf.byname[section]);fresh=(gnu_output/('gnu-'+section[1:]+'.bin')).read_bytes()
        require(actual==fresh,'Fresh GNU/independent ELF section mismatch')
        sections[section]={'length':len(actual),'sha256':sha(actual)}
    immutable,initialized,flags=[],[],{}
    for segment in elf.ph:
        if segment['type']!=1:continue
        lo=bias+segment['vaddr'];hi=lo+segment['memory_size']
        require(segment['file_size']<=segment['memory_size'],'PT_LOAD file/memory extent mismatch')
        if segment['flags']&2:initialized.append([lo,hi])
        else:
            require(segment['file_offset']==segment['vaddr'],'Formal immutable file-map correspondence mismatch')
            immutable.append([lo,lo+segment['file_size']])
        for page in range(lo//4096*4096,(hi+4095)//4096*4096,4096):flags[page]=flags.get(page,0)|segment['flags']
    relro,=[p for p in elf.ph if p['type']==0x6474e552]
    for page in range((bias+relro['vaddr'])//4096*4096,(bias+relro['vaddr']+relro['memory_size'])//4096*4096,4096):flags[page]&=~2
    def merge(pages):
        spans=[]
        for page in sorted(pages):
            if spans and spans[-1][1]==page:spans[-1][1]=page+4096
            else:spans.append([page,page+4096])
        return spans
    require(not any(not f&4 for f in flags.values()),'Formal image assumes readable mapped pages')
    mapped=merge(flags);execute=merge(p for p,f in flags.items() if f&1);write=merge(p for p,f in flags.items() if f&2)
    def interval(lo,hi):return f'0x{lo:x}<=a /\\ a<0x{hi:x}'
    for name,spans in [('c3_image_domain',mapped),('c3_image_execute',execute),('c3_image_write',write),('c3_immutable',immutable),('c3_initialized_rw',initialized)]:
        body=interval(*spans[0]) if len(spans)==1 else ' \\/ '.join('('+interval(*s)+')' for s in spans)
        require(compact(definitions[name])==compact(name+' a <=> '+body),'Formal image interval mismatch: '+name)
    require(immutable==inventory['image']['immutable_file_backed_intervals'] and initialized==inventory['image']['initialized_rw_intervals'],'Inventory/image interval mismatch')
    return dict(status='PASS_FRESH_TRUSTED_C3_BYTES_LINKAGE_IMAGE_SOURCE_CROSSCHECK_NOT_PROOF',artifact_sha256=elf.sha256,caller_sha256=sha(code),linkage=links,fresh_GNU=True,section_crosschecks=sections,immutable=immutable,initialized_rw=initialized,mapped=mapped,executable=execute,writable=write,GNU_program_headers_relocations_version_checked=True,parser_loader_physical_ISA_proof=False,target_routine_executed=False)
