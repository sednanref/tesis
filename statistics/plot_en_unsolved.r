#Script to plot the nodes expanded between heuristics for problems unsolved.

#Remove all the previous variables...
rm(list = ls())

# X and Y variables to plot an exact diagonal.
x <- c(-100, 3000000)
y <- c(-100, 3000000)

#NC + LM vs enhanced DR.
en <- read.csv(file = "Rate_Nodes - DR8h flow30min.csv")
dr_t_en <- en[,2]
nc_lm_en <- en[,3]
pdf("./graphics/en_nc_lm_vs_dr_t_unsolved.pdf")
plot(nc_lm_en,dr_t_en, xlim = c(0,2000000), ylim = c(0,2000000), pch=3, xlab = "NC + LM", ylab = expression("DR"^"m"),font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
par(new = TRUE)
plot(x, y, xlab="", ylab = "", xlim = c(0,2000000), ylim = c(0,2000000), type = "l", col = "red",font=2,font.lab=2, cex.axis=1.5,cex.lab=1.6)
#title("Expanded Nodes (Unsolved Problems)")
dev.off()