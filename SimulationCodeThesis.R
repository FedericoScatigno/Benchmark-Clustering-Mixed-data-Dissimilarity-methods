# ==============================================================================
# SIMULATION STUDY: COMPARING CLUSTERING METHODS FOR MIXED-TYPE DATA
# ==============================================================================

# ------------------------------------------------------------------------------
# PACKAGES
# ------------------------------------------------------------------------------
library(MixSim)        # Gaussian mixture generation
library(cluster)       # PAM algorithm
library(mclust)        # ARI calculation
library(caret)         # Dummy encoding
library(fpc)           # Hennig-Liao factors
library(data.table)    
library(dplyr)         

# ------------------------------------------------------------------------------
# CATEGORICAL DATA GENERATION
# ------------------------------------------------------------------------------

# Calculate Bhattacharyya coefficient for two probability vectors
pairwise_BC <- function(p1, p2) {
  if (length(p1) != length(p2)) stop("Vectors must have same length")
  sum(sqrt(p1 * p2))
}

# Average BC across all cluster pairs
Avg_BC <- function(prob_matrix) {
  K <- nrow(prob_matrix)
  n_pairs <- choose(K, 2)
  bc_values <- numeric(n_pairs)
  idx <- 1
  
  for (i in 1:(K-1)) {
    for (j in (i+1):K) {
      bc_values[idx] <- pairwise_BC(prob_matrix[i, ], prob_matrix[j, ])
      idx <- idx + 1
    }
  }
  mean(bc_values)
}

# Core function: generate K probability vectors with target overlap
gen_cat_param <- function(K, I, BC_target, marginal_type = "uniform", 
                          max_iter = 1000, tol = 0.01) {
  
  prob_matrix <- matrix(0, nrow = K, ncol = I)
  
  # UNIFORM CASE: each cluster concentrates on one primary level
  if (marginal_type == "uniform") {
    # Start with random concentrations
    conc <- runif(K, 0.3, 0.9)
    
    for (k in 1:K) {
      primary_level <- ((k - 1) %% I) + 1
      prob_matrix[k, primary_level] <- conc[k]
      prob_matrix[k, -primary_level] <- (1 - conc[k]) / (I - 1)
    }
    
    # Adjust until we hit target BC
    for (iter in 1:max_iter) {
      current_BC <- Avg_BC(prob_matrix)
      diff <- current_BC - BC_target
      
      if (abs(diff) < tol) {
        return(list(prob_matrix = prob_matrix, 
                    achieved_BC = current_BC, 
                    converged = TRUE))
      }
      
      # Step size depends on how far we are
      step_size <- min(0.05, max(0.005, abs(diff) * 0.3))
      
      # Move all concentrations together
      conc <- if (diff > 0) conc + step_size else conc - step_size
      conc <- pmax(1/I + 0.05, pmin(0.98, conc))
      
      # Rebuild matrix
      for (k in 1:K) {
        primary_level <- ((k - 1) %% I) + 1
        prob_matrix[k, primary_level] <- conc[k]
        prob_matrix[k, -primary_level] <- (1 - conc[k]) / (I - 1)
      }
    }
  } 
  
  # SKEWED CASE: geometric decay, different rate per cluster
  else {
    # Each cluster gets a random decay rate
    rates <- runif(K, 0.3, 0.7)
    base_probs <- vector("list", K)
    
    for (k in 1:K) {
      # Create geometric sequence
      p <- rates[k]^(0:(I-1))
      p <- p / sum(p)
      
      # Rotate for variety
      shift <- (k - 1) %% I
      base_probs[[k]] <- c(tail(p, shift), head(p, I - shift))
    }
    
    prob_matrix <- do.call(rbind, base_probs)
    base_BC <- Avg_BC(prob_matrix)
    uniform_p <- rep(1/I, I)
    
    # If we start too overlapped, make distributions peakier
    if (base_BC > BC_target + tol) {
      for (attempt in 1:50) {
        rates <- pmax(0.01, rates * 0.9)
        for (k in 1:K) {
          p <- rates[k]^(0:(I-1))
          p <- p / sum(p)
          shift <- (k - 1) %% I
          base_probs[[k]] <- c(tail(p, shift), head(p, I - shift))
        }
        base_BC <- Avg_BC(do.call(rbind, base_probs))
        if (base_BC <= BC_target + tol) break
      }
    }
    
    # Binary search: blend base distributions with uniform
    lo <- 0
    hi <- 1
    
    for (iter in 1:max_iter) {
      blend <- (lo + hi) / 2
      
      test_matrix <- matrix(0, K, I)
      for (k in 1:K) {
        test_matrix[k, ] <- blend * uniform_p + (1 - blend) * base_probs[[k]]
        test_matrix[k, ] <- test_matrix[k, ] / sum(test_matrix[k, ])
      }
      
      test_BC <- Avg_BC(test_matrix)
      
      if (abs(test_BC - BC_target) < tol) {
        return(list(prob_matrix = test_matrix, 
                    achieved_BC = test_BC, 
                    converged = TRUE))
      }
      
      if (test_BC > BC_target) hi <- blend else lo <- blend
      if (abs(hi - lo) < 1e-7) break
      
      prob_matrix <- test_matrix
    }
  }
  
  list(prob_matrix = prob_matrix, 
       achieved_BC = Avg_BC(prob_matrix), 
       converged = FALSE)
}

# Wrapper: generate multiple categorical variables
generate_categorical_data <- function(true_labels, K, p_cat, I_levels, 
                                      BC_target, marginal_type) {
  n <- length(true_labels)
  data_matrix <- matrix(NA, n, p_cat)
  
  for (var in 1:p_cat) {
    # Get probability matrix
    params <- gen_cat_param(K, I_levels, BC_target, marginal_type)
    
    # Sample for each cluster
    for (clust in 1:K) {
      in_cluster <- which(true_labels == clust)
      data_matrix[in_cluster, var] <- sample(1:I_levels, 
                                             length(in_cluster), 
                                             replace = TRUE, 
                                             prob = params$prob_matrix[clust, ])
    }
  }
  
  # Convert to factors
  df <- as.data.frame(data_matrix)
  for (j in 1:p_cat) {
    df[, j] <- factor(df[, j], levels = as.character(1:I_levels))
  }
  colnames(df) <- paste0("V", 1:p_cat)
  
  list(data = df, achieved_BC = params$achieved_BC)
}

# ------------------------------------------------------------------------------
# EMPIRICAL GOWER WEIGHTING
# ------------------------------------------------------------------------------

emp_avg_weight <- function(df_mixed, cat_indices, num_indices, phi = 0.5) {
  # Estimates weight to balance categorical and numeric contributions
  
  n <- nrow(df_mixed)
  
  # Sample pairs (faster than all pairs)
  n_pairs <- min(10000, choose(n, 2))
  i_idx <- sample.int(n, n_pairs, replace = TRUE)
  offset <- sample.int(n - 1, n_pairs, replace = TRUE)
  j_idx <- ((i_idx - 1 + offset) %% n) + 1
  
  # Average numeric dissimilarity 
  mu_num <- mean(sapply(num_indices, function(col) {
    vec <- as.numeric(df_mixed[[col]])
    rng <- diff(range(vec))
    if (rng > 0) mean(abs(vec[i_idx] - vec[j_idx]) / rng) else 0
  }))
  
  # Average categorical dissimilarity 
  mu_cat <- mean(sapply(cat_indices, function(col) {
    vec <- df_mixed[[col]]
    mean(vec[i_idx] != vec[j_idx])
  }))
  
  # Return weight
  list(w_block = phi * mu_num / max(mu_cat, 1e-12))
}

# ------------------------------------------------------------------------------
# SIMULATION SETUP
# ------------------------------------------------------------------------------

n <- 400                                  # Fixed sample size
nreps <- 1                                # Replications
cluster_sizes <- c(3)#, 5, 8)               
overlap_levels <- c(0.01)#, 0.05, 0.1)      # Continuous overlap
p_tot <- c(8)#, 14)                         
cat_ratios <- c(0.3)#, 0.5, 0.7)            # Proportion of categorical vars
I_set <- c(3)#, 5, 7)                       # Number of levels
sph_options <- c(TRUE, FALSE)             
skew_options <- c("uniform", "skewed")    
cat_BC_levels <- c(0.5, 0.7, 0.9)         # Categorical overlap

# Method settings
phi <- 0.5                                
cat_weight <- c(0.25, 0.5, 0.75)          
c_onehot <- c(1, 1.5, 2)                  

cat(sprintf("Total scenarios: %d\n", 
            nreps * length(cluster_sizes) * length(overlap_levels) * 
              length(p_tot) * length(cat_ratios) * length(I_set) * 
              length(sph_options) * length(skew_options) * length(cat_BC_levels)))

# ------------------------------------------------------------------------------
# MAIN LOOP
# ------------------------------------------------------------------------------

results_list <- list()
result_counter <- 1

for (seed_i in 1:nreps) {
  set.seed(1000 + seed_i)
  
  for (K in cluster_sizes) {
    for (overlap in overlap_levels) {
      for (p in p_tot) {
        for (prop_cat in cat_ratios) {
          for (I_levels in I_set) {
            for (sph_status in sph_options) {
              for (skew_choice in skew_options) {
                for (BC_target in cat_BC_levels) {
                  
                  cat(sprintf(
                    "seed=%d, K=%d, num overlap=%.2f, p=%d, prop cat=%.1f, level cat=%d, spherical=%s, type cat=%s, BC_target=%.2f\n",
                    seed_i, K, overlap, p, prop_cat, I_levels, sph_status, skew_choice, BC_target))
                  
                  # DATA GENERATION
                  n_cat <- round(p * prop_cat)
                  n_num <- p - n_cat
                  cat_indices <- 1:n_cat
                  num_indices <- (n_cat + 1):p
                  
                  # Continuous part
                  if (n_num > 0) {
                    mixsim_list <- MixSim(BarOmega = overlap, K = K, p = n_num, 
                                          sph = sph_status, PiLow = 1)
                    mixsim_temp <- simdataset(n, mixsim_list$Pi, 
                                              mixsim_list$Mu, mixsim_list$S)
                    df_numeric <- as.data.frame(mixsim_temp$X)
                    true_labels <- mixsim_temp$id
                  } else {
                    df_numeric <- data.frame(matrix(ncol = 0, nrow = n))
                    true_labels <- rep(1:K, length.out = n)
                  }
                  
                  # Categorical part
                  if (n_cat > 0) {
                    cat_result <- generate_categorical_data(
                      true_labels, K, n_cat, I_levels, BC_target, skew_choice
                    )
                    df_categorical <- cat_result$data
                    cat_BC_achieved <- cat_result$achieved_BC
                  } else {
                    df_categorical <- data.frame(matrix(ncol = 0, nrow = n))
                    cat_BC_achieved <- NA
                  }
                  
                  # Combine
                  df_mixed <- cbind(df_categorical, df_numeric)
                  colnames(df_mixed) <- paste0("V", 1:p)
                  
                  # CLUSTERING METHODS
                  
                  # Unweighted Gower
                  unw_diss <- daisy(df_mixed, metric = "gower")
                  pam_unw <- pam(unw_diss, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                  
                  results_list[[result_counter]] <- list(
                    seed = seed_i, spherical = sph_status, nClust = K, 
                    overlap = overlap, cat_BC_target = BC_target, 
                    cat_BC_achieved = cat_BC_achieved, ncols = p, 
                    catratio = prop_cat, catlevels = I_levels, 
                    skewcat = skew_choice, method = "Unweighted Gower (PAM)",
                    ARI = adjustedRandIndex(pam_unw, true_labels)
                  )
                  result_counter <- result_counter + 1
                  
                  # Fixed weights
                  for (w in cat_weight) {
                    w_vec <- c(rep(w, n_cat), rep(1, n_num))
                    w_diss <- daisy(df_mixed, metric = "gower", weights = w_vec)
                    pam_w <- pam(w_diss, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                    
                    results_list[[result_counter]] <- list(
                      seed = seed_i, spherical = sph_status, nClust = K, 
                      overlap = overlap, cat_BC_target = BC_target, 
                      cat_BC_achieved = cat_BC_achieved, ncols = p, 
                      catratio = prop_cat, catlevels = I_levels, 
                      skewcat = skew_choice, 
                      method = paste0("wcat=", w, " Gower (PAM)"),
                      ARI = adjustedRandIndex(pam_w, true_labels)
                    )
                    result_counter <- result_counter + 1
                  }
                  
                  # Empirical weighting
                  if (n_cat > 0 && n_num > 0) {
                    w_emp <- emp_avg_weight(df_mixed, cat_indices, num_indices, phi)$w_block
                    w_emp_vec <- c(rep(w_emp, n_cat), rep(1, n_num))
                    emp_diss <- daisy(df_mixed, metric = "gower", weights = w_emp_vec)
                    pam_emp <- pam(emp_diss, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                    
                    results_list[[result_counter]] <- list(
                      seed = seed_i, spherical = sph_status, nClust = K, 
                      overlap = overlap, cat_BC_target = BC_target, 
                      cat_BC_achieved = cat_BC_achieved, ncols = p, 
                      catratio = prop_cat, catlevels = I_levels, 
                      skewcat = skew_choice, 
                      method = "Empirical avg weight Gower (PAM)",
                      ARI = adjustedRandIndex(pam_emp, true_labels)
                    )
                    result_counter <- result_counter + 1
                  }
                  
                  # ENCODING METHODS
                  
                  if (n_cat > 0 && n_num > 0) {
                    # One-hot encoding
                    dmy <- dummyVars(~ ., data = df_mixed[, cat_indices, drop = FALSE], 
                                     fullRank = FALSE)
                    onehot_mat <- as.matrix(predict(dmy, df_mixed[, cat_indices, drop = FALSE]))
                    num_scaled <- scale(df_mixed[, num_indices, drop = FALSE])
                    
                    # Try different multipliers
                    for (c_val in c_onehot) {
                      combined <- cbind(onehot_mat * c_val, num_scaled)
                      dist_enc <- dist(combined, method = "manhattan")
                      pam_enc <- pam(dist_enc, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                      
                      results_list[[result_counter]] <- list(
                        seed = seed_i, spherical = sph_status, nClust = K, 
                        overlap = overlap, cat_BC_target = BC_target, 
                        cat_BC_achieved = cat_BC_achieved, ncols = p, 
                        catratio = prop_cat, catlevels = I_levels, 
                        skewcat = skew_choice, 
                        method = paste0("{0-", c_val, "} encoding (PAM)"),
                        ARI = adjustedRandIndex(pam_enc, true_labels)
                      )
                      result_counter <- result_counter + 1
                    }
                    
                    # Hennig-Liao with uniform assumption
                    hl_unif <- distancefactor(I_levels, n, type = "categorical", qfactor = 0.5)
                    combined_hl_unif <- cbind(onehot_mat * hl_unif, num_scaled)
                    dist_hl_unif <- dist(combined_hl_unif, method = "manhattan")
                    pam_hl_unif <- pam(dist_hl_unif, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                    
                    results_list[[result_counter]] <- list(
                      seed = seed_i, spherical = sph_status, nClust = K, 
                      overlap = overlap, cat_BC_target = BC_target, 
                      cat_BC_achieved = cat_BC_achieved, ncols = p, 
                      catratio = prop_cat, catlevels = I_levels, 
                      skewcat = skew_choice, method = "HL uniform probs (PAM)",
                      ARI = adjustedRandIndex(pam_hl_unif, true_labels)
                    )
                    result_counter <- result_counter + 1
                    
                    # Hennig-Liao with estimated probabilities
                    catsizes <- colSums(onehot_mat[, 1:I_levels, drop = FALSE])
                    hl_est <- distancefactor(I_levels, catsizes = catsizes, 
                                             type = "categorical", qfactor = 0.5)
                    combined_hl_est <- cbind(onehot_mat * hl_est, num_scaled)
                    dist_hl_est <- dist(combined_hl_est, method = "manhattan")
                    pam_hl_est <- pam(dist_hl_est, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                    
                    results_list[[result_counter]] <- list(
                      seed = seed_i, spherical = sph_status, nClust = K, 
                      overlap = overlap, cat_BC_target = BC_target, 
                      cat_BC_achieved = cat_BC_achieved, ncols = p, 
                      catratio = prop_cat, catlevels = I_levels, 
                      skewcat = skew_choice, method = "HL estimated probs (PAM)",
                      ARI = adjustedRandIndex(pam_hl_est, true_labels)
                    )
                    result_counter <- result_counter + 1
                    
                    # Z-standardize dummies
                    z_scaled <- scale(onehot_mat)
                    combined_z <- cbind(z_scaled, num_scaled)
                    dist_z <- dist(combined_z, method = "manhattan")
                    pam_z <- pam(dist_z, k = K, diss = TRUE, do.swap = FALSE, cluster.only = TRUE)
                    
                    results_list[[result_counter]] <- list(
                      seed = seed_i, spherical = sph_status, nClust = K, 
                      overlap = overlap, cat_BC_target = BC_target, 
                      cat_BC_achieved = cat_BC_achieved, ncols = p, 
                      catratio = prop_cat, catlevels = I_levels, 
                      skewcat = skew_choice, 
                      method = "Z-standardize {0-1} columns (PAM)",
                      ARI = adjustedRandIndex(pam_z, true_labels)
                    )
                    result_counter <- result_counter + 1
                  }
                }
              }
            }
          }
        }
      }
    }
  }
}

# Save
final_result <- rbindlist(results_list)
