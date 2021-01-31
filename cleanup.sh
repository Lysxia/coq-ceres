#!/bin/sh
URL="https://github.com/Lysxia/coq-ceres"
sed "s%href=\"../\"%href=\"$URL\"%" -i docs/*.html
