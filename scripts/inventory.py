#!/usr/bin/env python3
"""Inspect frozen ELF64 inputs with a small independently written parser.

The parser and GNU binutils crosscheck are discovery/binding tools in the trust
inventory. Neither is presented as a formally verified ELF loader.
"""
import argparse
import hashlib
import json
import pathlib
import re
import struct

ROOT = pathlib.Path(__file__).resolve().parents[1]
OUT = ROOT / "inventory"
def digest(data): return hashlib.sha256(data).hexdigest()
def save(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")

class ELF:
    def __init__(self,path):
        self.path=path; self.data=path.read_bytes(); self.sha256=digest(self.data)
        if self.data[:6]!=b"\x7fELF\x02\x01": raise ValueError("only ELF64 little-endian accepted")
        h=struct.unpack_from("<HHIQQQIHHHHHH",self.data,16)
        self.type,self.machine,_,self.entry,self.phoff,self.shoff,self.flags,_,self.phentsize,self.phnum,self.shentsize,self.shnum,self.shstrndx=h
        if self.machine!=62: raise ValueError("not x86-64")
        self.ph=[]
        for i in range(self.phnum):
            t,f,o,v,p,fs,ms,a=struct.unpack_from("<IIQQQQQQ",self.data,self.phoff+i*self.phentsize)
            self.ph.append(dict(type=t,flags=f,file_offset=o,vaddr=v,paddr=p,file_size=fs,memory_size=ms,align=a,permissions="".join(c for b,c in [(4,"R"),(2,"W"),(1,"X")] if f&b)))
        self.sections=[]
        for i in range(self.shnum):
            n,t,f,a,o,z,l,j,al,es=struct.unpack_from("<IIQQQQIIQQ",self.data,self.shoff+i*self.shentsize)
            self.sections.append(dict(name_offset=n,type=t,flags=f,vaddr=a,file_offset=o,size=z,link=l,info=j,align=al,entry_size=es))
        names=self.bytes(self.sections[self.shstrndx])
        for s in self.sections: s["name"]=self.string(names,s["name_offset"])
        self.byname={s["name"]:s for s in self.sections}
        self.symbols=[]; self.symbol_tables={}
        version_names=self.version_names()
        ver=self.bytes(self.byname[".gnu.version"]) if ".gnu.version" in self.byname else b""
        for s in self.sections:
            if s["type"] not in (2,11): continue
            strings=self.bytes(self.sections[s["link"]]); table=[]
            for i in range(s["size"]//s["entry_size"]):
                n,info,other,shndx,value,size=struct.unpack_from("<IBBHQQ",self.data,s["file_offset"]+i*s["entry_size"])
                sym=dict(name=self.string(strings,n),index=i,table=s["name"],binding=info>>4,type=info&15,visibility=other&3,section_index=shndx,vaddr=value,size=size)
                if s["type"]==11 and len(ver)>=2*(i+1):
                    vi=struct.unpack_from("<H",ver,2*i)[0]; sym.update(version_index=vi&0x7fff,version_hidden=bool(vi&0x8000),version=version_names.get(vi&0x7fff))
                table.append(sym); self.symbols.append(sym)
            self.symbol_tables[s["name"]]=table
        self.relocations=[]
        for s in self.sections:
            if s["type"] not in (4,9): continue
            syms=self.symbol_tables.get(self.sections[s["link"]]["name"],[])
            for i in range(s["size"]//s["entry_size"]):
                off,info=struct.unpack_from("<QQ",self.data,s["file_offset"]+i*s["entry_size"])
                si=info>>32; r=dict(section=s["name"],offset=off,type=info&0xffffffff,symbol_index=si,symbol=syms[si]["name"] if si<len(syms) else None)
                if s["type"]==4: r["addend"]=struct.unpack_from("<q",self.data,s["file_offset"]+i*s["entry_size"]+16)[0]
                self.relocations.append(r)
        self.dynamic=[]; self.build_id=None
        for s in self.sections:
            if s["type"]==6:
                strings=self.bytes(self.sections[s["link"]])
                for i in range(s["size"]//s["entry_size"]):
                    t,v=struct.unpack_from("<qQ",self.data,s["file_offset"]+i*s["entry_size"])
                    r=dict(tag=t,value=v)
                    if t in (1,14,15,29): r["string"]=self.string(strings,v)
                    self.dynamic.append(r)
            if s["type"]==7:
                b=self.bytes(s); at=0
                while at+12<=len(b):
                    ns,ds,t=struct.unpack_from("<III",b,at); at+=12
                    n=b[at:at+ns]; at+=(ns+3)&~3; desc=b[at:at+ds]; at+=(ds+3)&~3
                    if n.rstrip(b"\0")==b"GNU" and t==3: self.build_id=desc.hex()
    @staticmethod
    def string(b,n): return b[n:b.find(b"\0",n) if b.find(b"\0",n)>=0 else len(b)].decode("utf-8","replace")
    def bytes(self,s): return self.data[s["file_offset"]:s["file_offset"]+s["size"]]
    def version_names(self):
        names={0:"LOCAL",1:"GLOBAL"}
        for s in self.sections:
            if s["type"] not in (0x6ffffffd,0x6ffffffe): continue
            strings=self.bytes(self.sections[s["link"]]); b=self.bytes(s); at=0
            while at<len(b):
                if s["type"]==0x6ffffffd:
                    _,_,idx,_,_,aux,nxt=struct.unpack_from("<HHHHIII",b,at)
                    no,_=struct.unpack_from("<II",b,at+aux); names[idx]=self.string(strings,no)
                else:
                    _,count,_,aux,nxt=struct.unpack_from("<HHIII",b,at); aa=at+aux
                    for _ in range(count):
                        _,_,idx,no,anxt=struct.unpack_from("<IHHII",b,aa); names[idx]=self.string(strings,no)
                        if not anxt: break
                        aa+=anxt
                if not nxt: break
                at+=nxt
        return names
    def extract(self,va,n):
        choices=[p for p in self.ph if p["type"]==1 and p["vaddr"]<=va and va+n<=p["vaddr"]+p["file_size"]]
        if len(choices)!=1: raise ValueError("ambiguous or non-file-backed target region")
        p=choices[0]; off=p["file_offset"]+va-p["vaddr"]
        return off,self.data[off:off+n]

def main():
    ap=argparse.ArgumentParser(); ap.add_argument("--require-crosscheck",action="store_true"); args=ap.parse_args()
    artifact_paths=sorted((ROOT/"artifacts/baseline").rglob("*.so*"))
    artifacts=[]; byname={}; all_ok=True
    for path in artifact_paths:
        if not path.is_file(): continue
        e=ELF(path); byname[path.name]=e; stem=path.name
        save(OUT/"symbols"/(stem+".json"),e.symbols)
        save(OUT/"relocations"/(stem+".json"),e.relocations)
        cross=OUT/"raw"/(stem+".gnu-text.bin")
        s=e.byname.get(".text"); cross_ok=bool(s and cross.exists() and e.bytes(s)==cross.read_bytes())
        all_ok &= cross_ok
        artifacts.append(dict(artifact_sha256=e.sha256,path=str(path.relative_to(ROOT)),size=len(e.data),elf_build_id=e.build_id,architecture="x86-64",byte_order="little",abi="System V AMD64; ELF Linux",elf_type=e.type,entry=e.entry,loadable_segments=[p for p in e.ph if p["type"]==1],program_headers=e.ph,sections=e.sections,needed=[r["string"] for r in e.dynamic if r["tag"]==1],dynamic=e.dynamic,symbol_inventory="inventory/symbols/"+stem+".json",relocation_inventory="inventory/relocations/"+stem+".json",source_metadata_status="UNAVAILABLE in frozen ELF; see package provenance lock",debug_information_status="ELF has no matching debug file frozen",text_extraction_crosscheck=dict(status="PASS" if cross_ok else "NOT_CHECKED",independent_tool="GNU objcopy --dump-section .text",python_text_sha256=digest(e.bytes(s)) if s else None,gnu_text_sha256=digest(cross.read_bytes()) if cross.exists() else None,parser_formally_verified=False)))
    profile=json.loads((ROOT/"results/profile/baseline.json").read_text())
    spec_path=ROOT/"spec/CONTRACTS.md"
    contract_hash=digest(spec_path.read_bytes()) if spec_path.exists() else None
    selected=int(next(x["elf_vaddr"] for x in profile["symbols"] if x["symbol"]=="memcmp"),16)
    if selected!=0x152320: raise RuntimeError("profile drift: selected memcmp target differs from frozen baseline")
    targets=[("libcrypto.so.3","OPENSSL_cleanse",0x2417d0,97,"exported final ELF symbol extent"),("libcrypto.so.3","CRYPTO_memcmp",0x241840,95,"exported final ELF symbol extent"),("libc.so.6","memcmp_resolver",0x9bd80,113,"exported IFUNC symbol extent"),("libc.so.6","memcmp_baseline_avx2_movbe",selected,0x3ff,"discovery interval through last observed return; inferred extent, not a checked reachability proof")]
    regions=[]
    for fn,name,va,n,extent in targets:
        e=byname[fn]; off,b=e.extract(va,n); text=e.byname[".text"]
        cross=OUT/"raw"/(fn+".gnu-text.bin"); cb=cross.read_bytes()[va-text["vaddr"]:va-text["vaddr"]+n] if cross.exists() else None
        loaded=next((x for x in profile["symbols"] if int(x["elf_vaddr"],16)==va),None)
        load_ok=bool(loaded and loaded["first_32_bytes"]==b[:32].hex())
        (OUT/"regions").mkdir(parents=True,exist_ok=True); (OUT/"regions"/(name+".bin")).write_bytes(b)
        (OUT/"regions"/(name+".hex")).write_text(b.hex()+"\n")
        regions.append(dict(artifact_sha256=e.sha256,entry_point=name,implementation_variant=name,configuration_predicate="baseline-profile" if "baseline" in name or "resolver" in name else "unmodified Debian OpenSSL x86-64 assembly",contract_digest=contract_hash,contract_digest_kind="frozen human-readable requirements; formalization pending",contract_status="spec/freeze.json",elf_vaddr=va,file_offset=off,size=n,bytes_sha256=digest(b),bytes_hex=b.hex(),extraction_relationship="file_offset=PT_LOAD.p_offset+(elf_vaddr-PT_LOAD.p_vaddr)",extent_evidence=extent,gnu_byte_crosscheck="PASS" if cb==b else "NOT_CHECKED",runtime_prefix_check="PASS" if load_ok else "NOT_APPLICABLE",relocations_within_region=[r for r in e.relocations if va<=r["offset"]<va+n],reachable_helpers_observed=[],external_calls_observed=[],reachability_proof_status="NOT_PROVED",unique_covered_instruction_bytes=0,declared_region_bytes=n))
    save(OUT/"artifacts.json",dict(schema_version=1,provenance_class="unchanged production Debian packages in pinned local container image",artifacts=artifacts,parser_trust="small unverified Python ELF parser; crosschecked against GNU tools",crosscheck_status="PASS" if all_ok else "PARTIAL"))
    save(OUT/"targets.json",dict(schema_version=1,regions=regions,selected_baseline_profile="results/profile/baseline.json",dispatch_status="observed baseline selection only; machine-code selector proof pending"))
    raw_instructions={"OPENSSL_cleanse":"openssl-cleanse-instructions.txt","CRYPTO_memcmp":"crypto-memcmp-instructions.txt","memcmp_resolver":"glibc-resolver-instructions.txt","memcmp_baseline_avx2_movbe":"glibc-selected-instructions.txt"}
    instruction_groups=[]
    for region in regions:
        source=OUT/"raw"/raw_instructions[region["entry_point"]]
        ins=[]
        if source.exists():
            for line in source.read_text().splitlines():
                fields=line.split("\t")
                if len(fields)<3: continue
                addr_match=re.match(r"\s*([0-9a-f]+):",fields[0])
                if not addr_match: continue
                addr=int(addr_match[1],16); bs=bytes.fromhex(fields[1].strip()); asm=fields[2].strip()
                if not asm or not region["elf_vaddr"]<=addr<region["elf_vaddr"]+region["size"]: continue
                delta=addr-region["elf_vaddr"]
                if bytes.fromhex(region["bytes_hex"])[delta:delta+len(bs)]!=bs: raise ValueError("disassembly bytes drift")
                parts=asm.split(None,1); mnemonic=parts[0]; operand=parts[1] if len(parts)>1 else ""
                width=None
                for tag,w in (("YMMWORD PTR",32),("XMMWORD PTR",16),("QWORD PTR",8),("DWORD PTR",4),("WORD PTR",2),("BYTE PTR",1)):
                    if tag in operand: width=w;break
                target=re.match(r"([0-9a-f]+)\s*<",operand)
                ins.append(dict(elf_vaddr=addr,size=len(bs),bytes_hex=bs.hex(),mnemonic=mnemonic,operands=operand,explicit_memory_operand_width=width,direct_control_target=int(target[1],16) if target and (mnemonic.startswith("j") or mnemonic=="call") else None,implicit_stack_width=8 if "ret" in asm or mnemonic in ("push","pop","call") else None))
        instruction_groups.append(dict(artifact_sha256=region["artifact_sha256"],entry_point=region["entry_point"],source=str(source.relative_to(ROOT)),instructions=ins,mnemonics=sorted({x["mnemonic"] for x in ins}),status="DISASSEMBLY_DISCOVERY_ONLY",isa_qualification_status="backend assesses exact encodings; this is not semantics or control-flow proof"))
    save(OUT/"instructions.json",instruction_groups)
    save(OUT/"loading.json",dict(model="ELF64 PT_LOAD image with arbitrary consistent load bias; relocated writable segments are loader assumptions",immutable_code="RX PT_LOAD bytes fixed to frozen artifacts; no text relocations observed",zero_fill="PT_LOAD memory_size-file_size initialized zero",relocations="inventory/relocations per artifact",proved_loading="NOT_PROVED",baseline_runtime_observation="results/profile/baseline.json",permissions="declared page permissions by PT_LOAD; ordinary stable memory; no concurrency; return and stack separately specified",interposition="excluded by explicit postinitialization binding assumption"))
    client=ROOT/"clients/callers.so"
    if client.exists():
        e=ELF(client); rs=[]
        for sym in e.symbols:
            if sym["table"]==".dynsym" and sym["name"] in ("public_buffers_equal","secret_equal_and_clear"):
                off,b=e.extract(sym["vaddr"],sym["size"])
                rs.append(dict(entry_point=sym["name"],elf_vaddr=sym["vaddr"],file_offset=off,size=sym["size"],bytes_hex=b.hex(),bytes_sha256=digest(b),reachability_proof_status="NOT_PROVED"))
                (OUT/"regions"/(sym["name"]+".bin")).write_bytes(b)
                (OUT/"regions"/(sym["name"]+".hex")).write_text(b.hex()+"\n")
        bindings=[]; plt=e.byname[".plt"]
        for i,r in enumerate(r for r in e.relocations if r["section"]==".rela.plt"):
            va=plt["vaddr"]+16*(i+1);off,b=e.extract(va,16)
            bindings.append(dict(symbol=r["symbol"],got_elf_vaddr=r["offset"],plt_elf_vaddr=va,plt_file_offset=off,plt_bytes_hex=b.hex(),relocation=r,required_postinitialization_target={"memcmp":0x152320,"CRYPTO_memcmp":0x241840,"OPENSSL_cleanse":0x2417d0}.get(r["symbol"]),binding_status="observed runtime in diagnostics; formally unproved",lazy_resolution="excluded: DT_BIND_NOW and explicit initialized-GOT precondition"))
        cc={}
        for name in (".text",".plt"):
            path=OUT/"raw"/("callers.so.gnu-"+name[1:]+".bin")
            cc[name]="PASS" if path.exists() and e.bytes(e.byname[name])==path.read_bytes() else "NOT_CHECKED"
        save(OUT/"clients.json",dict(artifact_sha256=e.sha256,path="clients/callers.so",elf_build_id=e.build_id,source="clients/callers.c",build="clients/build.sh",headers="locks/client-toolchain.json",loadable_segments=[p for p in e.ph if p["type"]==1],needed=[r["string"] for r in e.dynamic if r["tag"]==1],dynamic=e.dynamic,symbols=e.symbols,relocations=e.relocations,caller_regions=rs,call_bindings=bindings,independent_gnu_section_crosscheck=cc,formal_proof_status="NOT_PROVED"))
    print(json.dumps(dict(artifact_count=len(artifacts),regions=len(regions),gnu_crosscheck="PASS" if all_ok else "PARTIAL",formal_proof_status="NOT_CLAIMED")))
    if args.require_crosscheck and not all_ok: raise SystemExit(1)
if __name__=="__main__": main()
