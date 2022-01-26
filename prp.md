## Target
* verified assembler中一个重要的pass是instruction encoding and decoding
    - CompCertELF是手写的encoder和decoder
    - CAV21 文章实现了一个自动生成encoder和decoder的框架
* 下一步的目标是将我们CAV21的工作移植到CompCertELF里
    - 原因是两个instruction的定义不同
    - 需要**实现**从CompCertELF的[```instruction```定义](https://github.com/SJTU-PLV/CompCert/blob/cav_ccelf/x86/Asm.v#L108)转换到CAV21自动生成的[```instruction```定义](https://github.com/SJTU-PLV/CompCert/blob/cav_ccelf/x86/TranslateInstr.v#L111)
* 在分支[**cav-ccelf**](https://github.com/SJTU-PLV/CompCert/tree/cav_ccelf)中的[```x86/TranslateInstr.v```](https://github.com/SJTU-PLV/CompCert/blob/cav_ccelf/x86/TranslateInstr.v)添加了一部分的指令转换

一些资料：
* x86指令的编码 [Encoding Real x86 Instructions](http://www.c-jump.com/CIS77/CPU/x86/lecture.html)
* CAV21的文章和代码 [encoder-n-decoder](https://github.com/SJTU-PLV/encoder-n-decoder/tree/cav21/artifact)
* [Intel指令手册](https://www.intel.com/content/www/us/en/developer/articles/technical/intel-sdm.html)
* GNU assembler的使用

## Step
* 先了解x86汇编，尝试写一些汇编代码然后用**as**进行编译
* 找出CompCertElf和CAV21两者对instruction定义的不同，并找出一一对应关系
* 完成transformation以及consistency证明
* 注意transformation需要用到[relocation table](https://github.com/SJTU-PLV/CompCert/blob/cav_ccelf/x86/TranslateInstr.v#L202)的信息，relocation table的作用可以看CSAPP ch7

### CompCert编译
选择32位的
```
./configure x86_32-linux
make
```
编译完后就可以跑```x86/TranslateInstr.v```了
