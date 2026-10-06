#!/usr/bin/env python3
"""C2 concrete frozen-source/literal checks; never a proof-success assertion.

Uses the unchanged lexical/path primitives from the accepted C1 checker. The
caller graph permits pinned generic nodes and C2 nodes, never C1-specific nodes.
"""
import hashlib,json,re,sys,types
from pathlib import Path
sys.dont_write_bytecode=True
OWN='development/approved-plan/reusable-assurance-v1'
SUCCESSOR='development/approved-plan/reusable-assurance-c2-v1'
CORE='development/approved-plan/reusable-assurance-c1-successor-v1/replay/source-check-v1.py'
CORE_SHA='4ce2c3fd384ad3d3100dd8a8a9d9050461091b2abc119edf3cba16ca44b7faf2'
PUBLIC='development/approved-plan/clients-e3/public-inputs-v1'
ANCHORS=SUCCESSOR+'/replay/anchors-v1.json'
HERE=Path(__file__).resolve().parent
def sha(path): return hashlib.sha256(Path(path).read_bytes()).hexdigest()
def module(path,name):
    obj=types.ModuleType(name);obj.__file__=str(path)
    exec(compile(path.read_bytes(),str(path),'exec'),obj.__dict__);return obj
ROOT=HERE.parents[3]
if sha(ROOT/CORE)!=CORE_SHA: raise ValueError('Changed pinned path/lexer checker primitives')
core=module(ROOT/CORE,'c2_pinned_path_lexer_primitives')
checked=core.checked; tokens=core.tokens; definition_literals=core.definition_literals
def anchor_data(root):
    data=json.loads(checked(root,ANCHORS).read_text())
    if data['schema']!='c2-source-anchors-v1' or data['status']!='FROZEN_SPEC_AND_WITNESS_IDENTITY_ANCHORS':
        raise ValueError('C2 specification/witness identity anchors absent/incomplete')
    for name,digest in data['files'].items(): checked(root,name,digest)
    if data['generic_inputs'][CORE]!=CORE_SHA: raise ValueError('Pinned checker primitive mismatch')
    for name,digest in data['generic_inputs'].items(): checked(root,name,digest)
    return data
def pairs(source,definitions=False):
    if definitions:return definition_literals(source)
    xs=re.findall(r'let\s+(\w+)\s*=\s*\x60([^\x60]*)\x60;;',source,re.S)
    if len(xs)!=len(dict(xs)):raise ValueError('Duplicate literal statement')
    return dict(xs)
def anchors(root):
    a=anchor_data(root)
    expected=json.loads(checked(root,a['expected_terms']).read_text())
    for name,literals in expected.items():
        path=SUCCESSOR+'/spec/'+name
        if pairs(checked(root,path).read_text(),name=='definitions-v1.ml')!=literals:
            raise ValueError('Frozen C2 literal/source mismatch: '+path)
    e5=json.loads(checked(root,a['e5_expected']).read_text())
    if len(e5['rows'])!=7:raise ValueError('Frozen E5 definition count mismatch')
    for row in e5['rows']:
        if hashlib.sha256(row['equation'].encode()).hexdigest()!=row['equation_sha256']:
            raise ValueError('Frozen E5 equation digest mismatch')
    witness=a['witness_registry']
    for path,digest in witness['files'].items():checked(root,path,digest)
    if pairs(checked(root,witness['statements_path']).read_text())!=witness['literal_targets']:
        raise ValueError('C2 pre-proof witness literal mismatch')
    return expected,e5
def resolve_import(root,name):
    a=anchor_data(root)
    if name.startswith('/reuse/'):
        path=OWN+'/'+name[len('/reuse/'):]
    elif name.startswith('/client-public/'):
        path=PUBLIC+'/'+name[len('/client-public/'):]
    elif name.startswith('/work/'):
        path=name[len('/work/'):]
    else:raise ValueError('Import has no reviewed mount mapping: '+name)
    if path in a['formal_generic_inputs']:return path
    if path.startswith(SUCCESSOR+'/') and path.endswith('.ml'):
        leaf=path[len(SUCCESSOR)+1:]
        if leaf.startswith(('spec/','proofs/','witnesses/','replay/c2-loader-')):return path
    raise ValueError('C2 graph imports excluded implementation/old caller/unpinned generic node: '+name)
def load_graph(root,loader):
    if not loader.startswith(SUCCESSOR+'/replay/c2-loader-') or not loader.endswith('.ml'):
        raise ValueError('C2 loader must belong to concrete C2 lane')
    graph,active={},set()
    def visit(name):
        if name in active:raise ValueError('Import cycle: '+name)
        if name in graph:return
        active.add(name);p=checked(root,name);source=p.read_text()
        if re.search(r'(?m)^\s*#\s*(?:use|load)\b',source):raise ValueError('Untracked toplevel import: '+name)
        imports,aliases=[],[];ts=tokens(source)
        for i,(kind,value) in enumerate(ts):
            if kind!='identifier':continue
            if value in ('new_axiom','mk_thm','Obj','new_type','new_constant'):
                raise ValueError('Unreviewed theorem/foundation bypass in C2 source: '+name)
            if value in ('use_file','use_file_no_raise','Toploop','Topdirs','Dynlink'):
                raise ValueError('Untracked direct/dynamic loader in C2 source: '+name)
            if value in ('needs','loadt','load_on_path'):
                if value=='load_on_path' or i+1==len(ts) or ts[i+1][0]!='string':raise ValueError('Dynamic import outside closed graph: '+name)
                imports.append(resolve_import(root,ts[i+1][1]));aliases.append(ts[i+1][1])
        graph[name]={'sha256':sha(p),'imports':imports,'import_mount_paths':aliases}
        for dependency in imports:visit(dependency)
        active.remove(name)
    visit(loader);return graph
def registry(root,mapping,graph=None):
    a=anchor_data(root);contract,e5=anchors(root)
    literals=contract['statements-v1.ml']
    if set(mapping)!=set(literals) or len(set(mapping.values()))!=len(literals):raise ValueError('Theorem map omits/duplicates frozen C2 targets')
    if any(not re.fullmatch(r'[A-Z][A-Za-z_0-9]*',v) for v in mapping.values()):raise ValueError('Unsafe theorem binding name')
    witness=a['witness_registry']
    def row(name,literal,**extra):return dict(name=name,literal=literal,expected_literal_sha256=hashlib.sha256(literal.encode()).hexdigest(),**extra)
    objects=[row(mapping[t],literal,target=t,category='original_c2',comparison='raw_closed_aconv') for t,literal in sorted(literals.items())]
    objects += [row(witness['theorem_map'][t],literal,target=t,category='nonvacuity_witness',comparison='raw_closed_aconv') for t,literal in sorted(witness['literal_targets'].items())]
    defs=dict(contract['definitions-v1.ml'])
    for source,source_defs in a['auxiliary_definitions'].items():
        if definition_literals(checked(root,source).read_text())!=source_defs:raise ValueError('Caller-specific auxiliary definition literal differs from its freeze')
        if set(defs)&set(source_defs):raise ValueError('Duplicate caller-specific auxiliary definition')
        defs.update(source_defs)
    for source,source_defs in witness['definitions'].items():
        if definition_literals(checked(root,source).read_text())!=source_defs:raise ValueError('Witness supporting definitions differ from pre-proof freeze')
        if set(defs)&set(source_defs):raise ValueError('Duplicate C2 supporting definition')
        defs.update(source_defs)
    definitions=[row(name,literal,comparison='SPEC_ALL_closed_type_variable_alpha_only') for name,literal in sorted(defs.items())]
    definitions += [dict(name=r['name'],literal=r['equation'],expected_literal_sha256=r['equation_sha256'],comparison=r['check_mode']) for r in e5['rows']]
    if len({r['name'] for r in objects+definitions})!=len(objects+definitions):raise ValueError('Overlapping theorem/definition names')
    if graph is not None:
        actual={}
        for path in graph:
            for name,literal in definition_literals(checked(root,path).read_text()).items():
                if name in actual:raise ValueError('Duplicate graph definition: '+name)
                actual[name]=literal
        expected={r['name']:r['literal'] for r in definitions}
        if actual!=expected:raise ValueError('Changed/unanchored/missing graph definition: '+repr(sorted(set(actual)^set(expected))))
    return dict(schema='c2-fresh-exact-registry-v1',objects=objects,definitions=definitions,original_target_count=len(literals),witness_target_count=len(witness['literal_targets']),nonvacuity_case_count=witness['nonvacuity_case_count'],caller_acceptance=False)
def validate_development_graph(root,seal):
    a=anchor_data(root);graph=load_graph(root,seal['loader'])
    if graph!=seal['graph'] or len(graph)!=seal['formal_graph_node_count']:raise ValueError('Changed frozen C2 graph')
    for path,row in graph.items():
        if path in a['formal_generic_inputs'] and row['sha256']!=a['formal_generic_inputs'][path]:raise ValueError('C2 changes pinned generic layer: '+path)
    if not seal['selected_main_proof_source'].startswith(SUCCESSOR+'/proofs/') or seal['selected_main_proof_source'] not in graph:raise ValueError('Main proof outside C2 graph')
    return dict(status='PINNED_GENERIC_AND_EXACT_CONCRETE_C2_GRAPH',node_count=len(graph),formal_dependency_isolation=False)
