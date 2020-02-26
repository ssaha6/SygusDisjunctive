# winner
# "--cegqi-si=none"

declare -a options=("--sygus-fair-max" "--sygus-fair=dt-height-bound"  "--sygus-fair=dt-size" "--sygus-fair=none" "--sygus-fair=direct" "--sygus-fair=dt-size-bound"  "--sygus-opt1" "--sygus-sym-break" "--sygus-sym-break-agg" "--sygus-sym-break-dynamic" "--sygus-sym-break-lazy" "--sygus-sym-break-pbe" "--sygus-sym-break-rlv"   "--sygus-active-gen=none" "--sygus-active-gen=enum" "--sygus-active-gen=basic" "--sygus-active-gen=var-agnostic" "--sygus-active-gen=auto" "--sygus-add-const-grammar" "--sygus-arg-relevant" "--sygus-auto-unfold" "--sygus-bool-ite-return-const" "--sygus-core-connective" "--sygus-crepair-abort" "--sygus-eval-opt" "--sygus-eval-unfold" "--sygus-eval-unfold-bool"  "--sygus-expr-miner-check-use-export" "--sygus-ext-rew" "--sygus-filter-sol-rev" " --sygus-filter-sol=strong" " --sygus-filter-sol=none" " --sygus-filter-sol=weak" "--sygus-grammar-cons=any-term" "--sygus-grammar-cons=any-const" "--sygus-grammar-cons=simple" "--sygus-grammar-cons=any-term-concise" "--sygus-grammar-norm" "--sygus-inference" "--sygus-inv-templ-when-sg"  "--sygus-min-grammar" "--sygus-pbe" "--sygus-pbe-multi-fair"  "--sygus-qe-preproc"  "--sygus-rec-fun"  "--sygus-ref-eval" "--sygus-repair-const"  "--sygus-sample-fp-uniform" "--sygus-sample-grammar"   "--sygus-templ-embed-grammar" "--sygus-unif-cond-independent-no-repeat-sol" "--sygus-unif-pi=none" "--sygus-unif-pi=cond-enum" "--sygus-unif-pi=complete" "--sygus-unif-pi=cond-enum-igain" "--sygus-unif-shuffle-cond" "--sygus-verify-subcall"  "--sygus-print-callbacks" "--cegis-sample=none" "--cegis-sample=trust" "--cegis-sample=use" "--cegqi" "--cegqi-si-abort" "--cegqi-si-partial"  "--cegqi-si-reconstruct-const"   "--cegqi-si=all" "--cegqi-si=use" "--cegqi-si-rcons=none" "--cegqi-si-rcons=all" "--cegqi-si-rcons=try" "--cegqi-si-rcons=all-limit" "--sygus-abort-size=1000000" "--sygus-repair-const-timeout=1000000" "--sygus-samples=1000000" "--sygus-pbe-multi-fair-diff=1000000" "--sygus-active-gen-cfactor=1000000" "--sygus-expr-miner-check-timeout=1000000" "--sygus-rec-fun-eval-limit=1000000"  "--cegqi-si-rcons-limit=1000000"  "--sygus-rr-synth-input-nvars=1000000"  "--sygus-abort-size=5" "--sygus-repair-const-timeout=5" "--sygus-samples=5" "--sygus-pbe-multi-fair-diff=5" "--sygus-active-gen-cfactor=5" "--sygus-expr-miner-check-timeout=5" "--sygus-rec-fun-eval-limit=5"  "--cegqi-si-rcons-limit=5"  "--sygus-rr-synth-input-nvars=5")


# multiple solutions
# "--sygus-rr"  

# did not stop
#  "--sygus-rr-synth" 
#   "--sygus-stream"

# other rrs
#  "--sygus-rr-synth-accel" "--sygus-rr-synth-check" "--sygus-rr-synth-filter-cong" "--sygus-rr-synth-filter-match" "--sygus-rr-synth-filter-nl" "--sygus-rr-synth-filter-order" "--sygus-rr-synth-input"  "--sygus-rr-synth-input-use-bool" "--sygus-rr-synth-rec" "--sygus-rr-verify" "--sygus-rr-verify-abort" 
 
 
 
# outputs all queries
# "--sygus-query-gen" "--sygus-query-gen-check" "--sygus-query-gen-dump-files=none" "--sygus-query-gen-dump-files=all" "--sygus-query-gen-dump-files=unsolved"  "--sygus-query-gen-thresh=4"

# mode
# "--sygus-inv-templ=MODE" "--sygus-out=MODE"



for opt in "${options[@]}" ; do 
    echo $opt; 
    output=`./cvc4-2020-02-06-win64-opt.exe   --lang=sygus2   $opt  sygus.sl`
    if [[ ${output} != *"let"* ]]; then
        echo ${output}
        read  -n 1 
    fi
done 


# cvc4 --option=help







