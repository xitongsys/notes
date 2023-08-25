# pulseaudio

`pacmd list-cards` list cards

`pactl load-module module-alsa-card`

load modules, it can have arguments.

On my computer, load HDMI card output using following cmd

`pactl load-module module-alsa-card device_id="0" name="pci-0000_01_00.1" card_name="alsa_card.pci-0000_01_00.1" namereg_fail=false tsched=yes fixed_latency_range=no ignore_dB=no deferred_volume=yes use_ucm=yes avoid_resampling=no card_properties="module-udev-detect.discovered=1"`


