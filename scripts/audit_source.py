#!/usr/bin/env python3
"""Static source inventory. Does not parse, elaborate, or check Lean proofs."""
from pathlib import Path
import argparse, json, re
from datetime import datetime, timezone
ROOT=Path(__file__).resolve().parents[1]

def strip_comments_strings(text):
    out=[]; i=0; depth=0; string=False
    while i<len(text):
        if depth:
            if text.startswith('/-',i): depth+=1; out.extend('  '); i+=2
            elif text.startswith('-/',i): depth-=1; out.extend('  '); i+=2
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif string:
            if text[i]=='\\': out.extend('  '); i+=2
            elif text[i]=='"': string=False; out.append(' '); i+=1
            else: out.append('\n' if text[i]=='\n' else ' '); i+=1
        elif text.startswith('/-',i): depth=1;out.extend('  ');i+=2
        elif text.startswith('--',i):
            j=text.find('\n',i)
            if j<0: j=len(text)
            out.extend(' '*(j-i));i=j
        elif text[i]=='"':string=True;out.append(' ');i+=1
        else:out.append(text[i]);i+=1
    return ''.join(out)

def inventory():
    rows=[]; bad=[]; decls=[]; goals=[]
    # Match the complete source traversal used by scripts/verify.py.
    for file in sorted((ROOT/'GS').rglob('*.lean')) + sorted(ROOT.glob('GS*.lean')):
        text=file.read_text();code=strip_comments_strings(text)
        rows.append({'file':str(file.relative_to(ROOT)), 'physical_lines':len(text.splitlines()),
                     'nonempty_code_lines':sum(bool(x.strip()) for x in code.splitlines())})
        stack=[]
        for lineno,line in enumerate(code.splitlines(),1):
            ns=re.match(r'^\s*namespace\s+([\w.]+)',line)
            sec=re.match(r'^\s*(?:noncomputable\s+)?section(?:\s+([\w.]+))?\s*$',line)
            end=re.match(r'^\s*end(?:\s+([\w.]+))?\s*$',line)
            if ns:stack.append(('namespace',ns.group(1)))
            elif sec:stack.append(('section',sec.group(1) or ''))
            elif end:
                if stack:
                    if end.group(1):
                        for k in range(len(stack)-1,-1,-1):
                            if stack[k][1]==end.group(1): del stack[k:];break
                    else:stack.pop()
            for kind,name in re.findall(r'\b(theorem|lemma|def|abbrev|structure)\s+([\w.]+)',line):
                full='.'.join([x[1] for x in stack if x[0]=='namespace']+[name])
                if kind in ('theorem','lemma'):
                    decls.append({'name':full,'file':str(file.relative_to(ROOT)),'line':lineno})
                if name.endswith('Goal'):
                    goals.append({'name':full,'file':str(file.relative_to(ROOT)),'line':lineno})
        for pat,label in [(r'\bsorry\b','sorry'),(r'\badmit\b','admit'),(r'\baxiom\b','axiom declaration'),
                          (r'\bsorryAx\b','sorryAx'),
                          (r'\bnative_decide\b','native_decide'),(r'\bunsafe\b','unsafe'),
                          (r'\bimplemented_by\b','implemented_by')]:
            for m in re.finditer(pat,code):
                bad.append({'file':str(file.relative_to(ROOT)), 'line':code[:m.start()].count('\n')+1,'kind':label})
    return {'audit_kind':'static_text_inventory_only', 'kernel_checked':False,
            'timestamp_utc':datetime.now(timezone.utc).isoformat(),
            'files':rows,'proof_body_declarations':decls,'goal_definitions':goals,
            'banned_constructs_in_code':bad,
            'physical_lean_lines':sum(x['physical_lines'] for x in rows),
            'proof_body_count':len(decls),
            'warning':'Absence of sorry/axiom does not imply elaboration, correct typing, or mathematical completion.'}

def main():
    parser=argparse.ArgumentParser();parser.add_argument('--write-audit-lean',action='store_true');args=parser.parse_args()
    data=inventory()
    out=ROOT/'.lake'/'verification'/'source'
    out.mkdir(parents=True, exist_ok=True)
    (out/'source_audit.json').write_text(json.dumps(data,ensure_ascii=False,indent=2))
    if args.write_audit_lean:
        # Do not feed heuristic names (notably private declarations) to #print.
        # The main verifier remains the authoritative build-and-audit command.
        modules = [row['file'][:-5].replace('/', '.') for row in data['files']]
        lines = ['module', *('import all ' + module for module in modules), 'import Lean', '',
                 'open Lean Elab Command', 'set_option maxHeartbeats 0', 'run_cmd do',
                 '  let modules : Array Name := #[' + ', '.join('`' + m for m in modules) + ']',
                 '  let env ← getEnv',
                 '  let names := env.constants.fold (init := (#[] : Array Name)) fun names name info =>',
                 '    match env.getModuleIdxFor? name with',
                 '    | some idx => if !info.isUnsafe && modules.contains env.header.moduleNames[idx]! then names.push name else names',
                 '    | none => names',
                 '  if names.isEmpty then throwError "No project declarations were found"',
                 '  for moduleName in modules do',
                 '    unless (env.getModuleIdx? moduleName).isSome do throwError "Missing module: {moduleName}"',
                 '  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]',
                 '  let mut axioms : NameSet := {}',
                 '  for name in names do',
                 '    for axiomName in (← Lean.collectAxioms name) do',
                 '      unless allowed.contains axiomName do throwError "Unexpected axiom: {axiomName}"',
                 '      axioms := axioms.insert axiomName',
                 '  logInfo m!"AUDIT_DECLARATIONS {names.size}"',
                 '  logInfo m!"AUDIT_AXIOMS {axioms.toList}"']
        (out/'Audit.lean').write_text('\n'.join(lines)+'\n')
    print(f"{len(data['files'])} modules; {data['physical_lean_lines']} lines; {data['proof_body_count']} theorem/lemma declarations.")
    print(f"{len(data['goal_definitions'])} Goal definitions; forbidden constructs: {len(data['banned_constructs_in_code'])}.")
    print('STATIC INVENTORY ONLY: run scripts/verify.py for compilation and axiom checking.')
    raise SystemExit(bool(data['banned_constructs_in_code']))
if __name__=='__main__':main()
