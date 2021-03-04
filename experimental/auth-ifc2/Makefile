SOUFFLE = souffle
SOUFFLE_ARGS = ''

example:
	$(SOUFFLE) moduleCheckExample.dl && \
		echo "flowsTo:" && cat flowsTo.csv && \
		echo "bindModule:" && cat bindModule.csv && \
		echo "moduleLabelChecks:" && cat moduleLabelChecks.csv

clean:
	rm *csv
