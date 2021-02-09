SOUFFLE = souffle
SOUFFLE_ARGS = ''

flowsToAxioms:
	$(SOUFFLE) flowsToAxioms_test.dl && \
		echo "trusts:" && cat trusts.csv && \
		echo "flowsTo:" && cat flowsTo.csv

flowsToSaysAxioms:
	$(SOUFFLE) flowsToSaysAxioms_test.dl && \
		echo "trusts:" && \
		echo "read x   y   z like x believes y trusts z " && \
		cat trusts.csv && \
		echo "flowsTo:" && \
		echo "read x   y   z like x believes y flowsTo z " && \
		echo "data movement is allowed from p to q if (top believes p flowsTo q)" && \
		cat flowsTo.csv

clean:
	rm *csv
