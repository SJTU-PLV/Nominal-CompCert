include ../Makefile.menhir

PYTHON = python3

correct:
	@ $(MENHIR) RustsurfaceParser.mly --list-errors --table > RustsurfaceParserM.auto.messages
	$(PYTHON) process_messages.py
	@ $(MENHIR) RustsurfaceParser.mly --table --compile-errors RustsurfaceParserM.messages > RustsurfaceParserM.ml

clean:
	rm -f RustsurfaceParser.automaton
	rm -f RustsurfaceParser.conflicts
	rm -f RustsurfaceParserM.auto.messages
	rm -f RustsurfaceParserM.messages