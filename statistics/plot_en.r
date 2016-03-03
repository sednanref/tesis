#Script to plot the nodes expanded between heuristics.

#Remove all the previous variables...
rm(list = ls())

# X and Y variables to plot an exact diagonal.
x <- c(-1e+7, 1e+20)
y <- c(-1e+7, 1e+20)

#enhanced DR vs normal DR
en <- read.csv(file = "../results/expanded_nodes_dr.1.1.2.1800.cplex_dr.0.0.0.1800.cplex.csv", header = FALSE)
dr_t_en <- en[,2]
dr_en <- en[,3]
pdf("./graphics/en_dr_t_vs_dr.pdf")
plot(dr_en, dr_t_en, xlim = c(0,1000), ylim = c(0,1000), xlab = "DR", ylab = expression("DR"^"m"), pch = 3,font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlab="", ylab = "", xlim = c(0,1000), ylim = c(0,1000), type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
#enhanced DR vs NC
en <- read.csv("../results/expanded_nodes_dr.1.1.2.1800.cplex_flow.00.1800.cplex.csv", header = FALSE)
dr_t_en <- en[,2]
nc_en <- en[,3]
pdf("./graphics/en_dr_t_vs_nc.pdf")
plot(nc_en, dr_t_en, xlim = c(0,1000), ylim = c(0,1000), xlab = "NC", ylab = expression("DR"^"m"), pch = 3,font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlab="", ylab = "", xlim = c(0,1000), ylim = c(0,1000), type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
#enhanced DR vs LM
en <- read.csv("../results/expanded_nodes_dr.1.1.2.1800.cplex_opt-part.2.1800.cplex.csv", header = FALSE)
dr_t_en <- en[,2]
lm_en <- en[,3]
pdf("./graphics/en_dr_t_vs_lm.pdf")
plot(lm_en, dr_t_en, xlim = c(0,1000), ylim = c(0,1000), xlab = "LM", ylab = expression("DR"^"m"), pch = 3,font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlab="", ylab = "", xlim = c(0,1000), ylim = c(0,1000), type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()
#enhanced DR vs NC + LM 
en <- read.csv("../results/expanded_nodes_dr.1.1.2.1800.cplex_flow.20.1800.cplex.csv", header = FALSE)
dr_t_en <- en[,2]
lm_en <- en[,3]
pdf("./graphics/en_dr_t_vs_nc_lm.pdf")
plot(lm_en, dr_t_en, xlim = c(0,1000), ylim = c(0,1000), xlab = "NC + LM", ylab = expression("DR"^"m"), pch = 3,font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlab="", ylab = "", xlim = c(0,1000), ylim = c(0,1000), type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
dev.off()