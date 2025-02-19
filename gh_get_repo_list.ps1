$allRepos = @()
$errorRepos = @()
$totalPage = 1
$perPage = 30
$totalCount = $totalPage * $perPage
$username = "YOUR_GITHUB_USERNAME"

do {
    try {
        $repos = gh repo list $username --json archivedAt,assignableUsers,codeOfConduct,contactLinks,createdAt,defaultBranchRef,deleteBranchOnMerge,description,diskUsage,forkCount,fundingLinks,hasDiscussionsEnabled,hasIssuesEnabled,hasProjectsEnabled,hasWikiEnabled,homepageUrl,id,isArchived,isBlankIssuesEnabled,isEmpty,isFork,isInOrganization,isMirror,isPrivate,isSecurityPolicyEnabled,isTemplate,isUserConfigurationRepository,issueTemplates,issues,labels,languages,latestRelease,licenseInfo,mentionableUsers,mergeCommitAllowed,milestones,mirrorUrl,name,nameWithOwner,openGraphImageUrl,owner,parent,primaryLanguage,projects,projectsV2,pullRequestTemplates,pullRequests,pushedAt,rebaseMergeAllowed,repositoryTopics,securityPolicyUrl,squashMergeAllowed,sshUrl,stargazerCount,templateRepository,updatedAt,url,usesCustomOpenGraphImage,viewerCanAdminister,viewerDefaultCommitEmail,viewerDefaultMergeMethod,viewerHasStarred,viewerPermission,viewerPossibleCommitEmails,viewerSubscription,visibility,watchers --visibility public --source --page $page | ConvertFrom-Json
        $allRepos += $repos
    } catch {
        $errorDetails = @{
            Page = $page
            ErrorMessage = $_.Exception.Message
        }
        $errorRepos += [pscustomobject]$errorDetails
    }
    $page++
} while ($allRepos.Count -le $totalCount)

# Sort the results by the 'url' field
$sortedRepos = $allRepos | Sort-Object url

# Save the sorted results to a file
$sortedRepos | ConvertTo-Json | Out-File -FilePath "all_repos_sorted.json"

# Save the error details to a separate file
$errorRepos | ConvertTo-Json | Out-File -FilePath "error_repos.json"


$allRepos = @()
$errorRepos = @()
$totalPage = 1
$perPage = 30
$totalCount = $totalPage * $perPage
$username = "YOUR_GITHUB_USERNAME"

do {
    try {
        $repos = gh repo list $username --json name, url --visibility public --source --page $page | ConvertFrom-Json
        $allRepos += $repos
    } catch {
        $errorDetails = @{
            Page = $page
            ErrorMessage = $_.Exception.Message
        }
        $errorRepos += [pscustomobject]$errorDetails
    }
    $page++
} while ($allRepos.Count -le $totalCount)

# Sort the results by the 'url' field
$sortedRepos = $allRepos | Sort-Object url

# Save the sorted results to a file
$sortedRepos | ConvertTo-Json | Out-File -FilePath "all_repos_sorted.json"

# Save the error details to a separate file
$errorRepos | ConvertTo-Json | Out-File -FilePath "error_repos.json"