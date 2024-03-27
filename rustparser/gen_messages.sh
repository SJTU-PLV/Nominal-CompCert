menhir RustsurfaceParser.mly --list-errors --table > RustsurfaceParserM.auto.messages
python process_messages.py
menhir RustsurfaceParser.mly --table --compile-errors RustsurfaceParserM.messages > RustsurfaceParserM.ml
