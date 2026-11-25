#!/bin/bash
# usage: judge_axioms.sh FILE...   (a saved Lean build log, or an extract of expected_output/)
# Verdict PASS iff: every `depends on axioms: [...]` line lists only propext, Classical.choice, Quot.sound;
# no line mentions sorryAx or ofReduceBool; no line starts with `error:`. Prints counts. Exit 1 on FAIL.
rc=0
for f in "$@"; do
  awk -v F="$f" '
    /depends on axioms: \[/ {
      s=$0; sub(/.*depends on axioms: \[/,"",s); sub(/\].*/,"",s); n=split(s,a,",");
      ok=1; for(i=1;i<=n;i++){ t=a[i]; gsub(/^ +| +$/,"",t); if(t!="propext" && t!="Classical.choice" && t!="Quot.sound") ok=0 }
      if(ok) good++; else {bad++; print F": NON-STANDARD: " $0}
    }
    /does not depend on any axioms/ {none++}
    /sorryAx|ofReduceBool/ {so++}
    /^error:/ {err++}
    END { printf "%s: std-subset=%d no-axioms=%d nonstandard=%d sorryAx/ofReduceBool=%d errors=%d -> %s\n", F, good, none, bad, so, err, (bad+so+err==0 && good+none>0)?"PASS":"FAIL"; exit !(bad+so+err==0 && good+none>0) }
  ' "$f" || rc=1
done
exit $rc
