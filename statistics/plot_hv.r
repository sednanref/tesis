#Script to plot the nodes expanded between heuristics.

#Remove all the previous variables...
rm(list = ls())

# X and Y variables to plot an exact diagonal.
x <- c(-100, 3000)
y <- c(-100, 3000)

#Variables 
HV <- read.csv("Heuristic_values2.csv")
dr_hv <- HV[,3]
dr_t_hv <- HV[,4]
nc_lm_hv <- HV[,5]
nc_hv <- HV[,6]
lm_hv <- HV[,7]

# DR vs DR enhanced.
pdf("./graphics/hv_dr_vs_dr_t.pdf")
plot(dr_hv, dr_t_hv, pch = 3, xlim = c(0,300), ylim = c(0,300), xlab = "DR", ylab = expression("DR"^"m"),font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlim = c(0,300), ylim = c(0,300), xlab = "", ylab = "", type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
# NC vs DR enhanced.
pdf("./graphics/hv_nc_vs_dr_t.pdf")
plot(nc_hv, dr_t_hv, pch = 3, xlim = c(0,300), ylim = c(0,300), xlab = "NC", ylab = expression("DR"^"m"),font=2,font.lab=2,cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlim = c(0,300), ylim = c(0,300), xlab = "", ylab = "", type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
# NC + LM vs DR enhanced.
pdf("./graphics/hv_nc_lm_vs_dr_t.pdf")
plot(nc_lm_hv, dr_t_hv, pch = 3, xlim = c(0,300), ylim = c(0,300), xlab = "NC + LM", ylab = expression("DR"^"m"),font=2,font.lab=2,cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlim = c(0,300), ylim = c(0,300), xlab = "", ylab = "", type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
# LM vs DR enhanced.
pdf("./graphics/hv_lm_vs_dr_t.pdf")
plot(lm_hv, dr_t_hv, pch = 3, xlim = c(0,300), ylim = c(0,300), xlab = "LM", ylab = expression("DR"^"m"),font=2,font.lab=2,cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlim = c(0,300), ylim = c(0,300), xlab = "", ylab = "", type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
