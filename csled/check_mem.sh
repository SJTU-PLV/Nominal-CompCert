+#!/bin/bash
+
+while true
+do
+       cat /proc/$1/status|grep VmPeak|tee -a record_$1.txt
+       sleep 600
+done
