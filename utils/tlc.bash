java -XX:+UseParallelGC -Xmx12g -cp ~/Downloads/tla2tools.jar tlc2.TLC \
    -workers 12 \
    -checkpoint 2 \
    -config TLA-plus-spec/JanusConfig.cfg TLA-plus-spec/Janus.tla | tee /dev/tty > janus-safety/tlc-model-check.txt