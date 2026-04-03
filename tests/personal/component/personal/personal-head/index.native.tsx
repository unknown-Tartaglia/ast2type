/* eslint-disable react/jsx-no-undef */
import React, { Component } from 'react';
import { Dimensions, View, DeviceEventEmitter, Animated } from 'react-native';
import {
  CommonUtils,
  componentautoscaling,
  Cookies,
  PlatformUtils,
  RouterUtils,
  screenSize as getScreenSize,
  t,
  WithTheme,
  DeviceUtils,
  itemExposeHoc,
  monitor,
  EventTracking,
  HttpService,
  Service as env,
  URL_CONSTANTS,
  ScreenUtils,
  SHARE_CHANNEL,
  LoginUtils,
  INTERNAL_JUMP_LINK,
  PAGE_TYPE,
} from '@hw-vmall/vrn-basic-comp';
import { ImageBackground as RNImageBackground } from '@hw-vmall/vrn-bussiness-comp';
import ImgArray from '../../../../../assets/ImgArray';
import IconList from '../../../../../component/basic1/title/components/IconList/index';
import dapReportList from './dapReportList';
import styles from './style/index_app';
import AnimationHeader from './animation';

let iosStatusBarHeight: number = 0;
if (PlatformUtils.isIOS()) {
  DeviceUtils.getStatusBarHeight()
    .then((result: any) => {
      iosStatusBarHeight = result;
    })
    .catch(() => {
      // do nothing
    });
}
class PersonalTitle extends Component<any, any> {
  shareInfo: any = null;
  addlist: any;
  scrollEmitter: any;
  titleAnimatedValue = new Animated.Value(1);
  userInfoAnimatedValue = new Animated.Value(0);
  isShowTitle = true;
  constructor(props) {
    super(props);
    this.state = {
      pageType: this.props.pageType || 'personal',
      iconList: [],
      backGroundStyle: null,
      canClick: true,
    };
  }
  componentDidMount() {
    this.getChangeStyle();
    const { headStyle } = this.props;
    headStyle && headStyle.iconTexts && headStyle.iconTexts.length !== 0
      ? this.handleIconList(headStyle.iconTexts)
      : null;
    this.scrollEmitter = DeviceEventEmitter.addListener(
      'onOutScrollViewScroll',
      (contentOffset: number, pageType: string) => {
        if (pageType !== PAGE_TYPE.personal) {
          return;
        }
        if (contentOffset <= 40 && !this.isShowTitle) {
          this.isShowTitle = true;
          Animated.timing(this.userInfoAnimatedValue, {
            toValue: 0,
            duration: 340,
            useNativeDriver: true,
          }).start(() => {
            Animated.timing(this.titleAnimatedValue, {
              toValue: !this.isShowTitle ? 0 : 1,
              duration: 80,
              useNativeDriver: true,
            }).start();
          });
          this.setState({ canClick: this.isShowTitle });
        }
        if (contentOffset > 40 && this.isShowTitle) {
          this.isShowTitle = false;
          Animated.timing(this.titleAnimatedValue, {
            toValue: 0,
            duration: 80,
            useNativeDriver: true,
          }).start(() => {
            Animated.timing(this.userInfoAnimatedValue, {
              toValue: this.isShowTitle ? 0 : 1,
              duration: 340,
              useNativeDriver: true,
            }).start();
          });
          this.setState({ canClick: this.isShowTitle });
        }
      },
    );
  }
  componentWillUnmount() {
    this.scrollEmitter && this.scrollEmitter.remove();
    this.addlist && this.addlist.remove();
  }

  /**
   * 处理所有标题数据
   * 返回数据源编号集合
   * @param list 标题icon数据源
   */
  handleIconList(list: Array<any>) {
    const ICON_NAME = PlatformUtils.isIOS()
      ? ['scan', 'personalCenter', 'message', 'homePage', 'search', 'setting', 'custom']
      : ['scan', 'cart', 'personalCenter', 'message', 'homePage', 'search', 'setting', 'userContentCenter', 'custom'];
    const iconList = list.map((item, index) => {
      return {
        iconUrl: item.iconAttribute === 'custom' ? env.cmsCndProdPath + item.imgUrl : item.iconAttribute + 'Show',
        iconText: this.handleIconText(item.iconAttribute, item.title),
        actionUrl: this.handleIconUrl(item.iconAttribute, item),
        iconNo: index + 1,
        gotoPageId: index + 1,
        clickType: this.handleListType(item.iconAttribute),
        isCart: item.iconAttribute === 'cart',
        isMessage: item.iconAttribute === 'message',
        listName: item.iconAttribute,
      };
    });
    const relList = iconList.filter((list) => {
      return ICON_NAME.includes(list.listName);
    });
    this.setState({
      iconList: relList.length > 10 ? relList.slice(0, 10) : relList,
    });
    // 读取配置参数有分享，则调用获取分享信息接口
    const hasShare = list.some((item) => {
      return item.iconAttribute === 'share';
    });
    hasShare && this.getShareInfo(iconList, ICON_NAME);
  }

  getShareInfo = (iconList, iconNams) => {
    const names = iconNams;
    HttpService.getShareLinkInfo(this.props?.pageId, '').then((res) => {
      const shareItem = res?.shareIcons?.length && res?.shareIcons[0];
      this.shareInfo = shareItem;
      if (shareItem && JSON.stringify(shareItem) !== '{}') {
        names.push('share');
      } else {
        return;
      }
      const relList = iconList.filter((list) => {
        return names.includes(list.listName);
      });
      relList.map((item) => {
        if (item?.iconUrl === 'shareShow') {
          item.iconUrl = shareItem?.shareType === '0' ? 'share' : 'ic_earnByShare';
        }
      });
      this.setState({
        iconList: relList.length > 10 ? relList.slice(0, 10) : relList,
      });
    });
  };

  /**
   * 打开分享弹窗
   */
  openShareDialog = async () => {
    const {
      shareTitle,
      weixinShareIcon,
      sharePoster,
      shareEarnTitle,
      shareContent,
      shareType,
      shareWapLink,
      shareAppLink,
    } = this.shareInfo;
    const shareInfoReq = {
      shareType: shareType === '0' ? '1' : '2',
      sharePosition: 'FromTitle',
      shareTips: shareEarnTitle,
      linkShareTo:
        PlatformUtils.isAndroid() || PlatformUtils.isHarmony()
          ? SHARE_CHANNEL.LINK_APK_CHANNELS
          : SHARE_CHANNEL.LINK_IOS_CHANNELS,
      posterShareTo: sharePoster ? SHARE_CHANNEL.POST_APK_CHANNELS : '',
      otherShareTo: '301',
      shortTitle: shareTitle,
      shortContent: shareContent,
      longContent: shareContent,
      picUrl: `${env.cmsCdnPath}${weixinShareIcon}`,
      wechatMpPicUrl: '',
      wechatMpPicData: {},
      shareWapUrl: shareWapLink,
      shareMpUrl: '',
      clientPosterMethodType: '',
      clientPosterParam: {},
    };
    if (shareType === '1') {
      const { cid = '', wi = '', mid = '' } = await this.getCpsUserInfo();
      let cpsInfo = '';
      if (mid !== '') {
        cpsInfo = `cid=${cid}&wi=mid:${mid},fid:9_${shareAppLink},cid:${cid},wi:9`;
      } else if (wi !== '' && wi.includes('mid')) {
        cpsInfo = `cid=${cid}&wi=${wi}`;
      }
      shareWapLink.includes('?')
        ? (shareInfoReq.shareWapUrl += cpsInfo && `&${cpsInfo}`)
        : (shareInfoReq.shareWapUrl += cpsInfo && `?${cpsInfo}`);
    }
    if (sharePoster) {
      shareInfoReq.clientPosterParam = {
        activityPicUrl: `${env.cmsCdnPath}${sharePoster}`,
        scanCodeType: '1',
        wapUrl: shareInfoReq.shareWapUrl,
      };
      shareInfoReq.clientPosterMethodType = '1';
    }
    const loadReportData = {
      pageId: shareAppLink,
      type: shareType === '0' ? '1' : '2',
    };
    const clickReportData = {
      pageId: shareAppLink,
      gotoURL: '',
      type: shareType === '0' ? '1' : '2',
    };
    const reportShareInfo = {
      loadReportKey: '100000811',
      loadReportData: JSON.stringify(loadReportData),
      clickReportKey: '100000810',
      clickReportData: JSON.stringify(clickReportData),
    };
    const shareData = { ...shareInfoReq, ...reportShareInfo };
    CommonUtils.pullShareDialog(JSON.stringify(shareData));
  };

  /**
   * 通过接口获取cid和wi
   */
  getCpsUserInfo = (): any => {
    return new Promise((resolve, reject) => {
      HttpService.getCpsUserInfo()
        .then((res) => {
          const { code, cpsUserInfo } = res || {};
          String(code) === '0' && resolve(cpsUserInfo);
        })
        .catch(() => {
          reject({});
        });
    });
  };

  /**
   * 点击分享赚需要实时判断登录状态
   */
  getIsLogin = () => {
    return new Promise((resolve, reject) => {
      LoginUtils.getLoginStatus()
        .then((isLogin: boolean) => {
          resolve(isLogin);
        })
        .catch(() => {
          reject(false);
        });
    });
  };

  handleIconText(text: string, title: any): any {
    switch (text) {
      case 'cart':
        // 购物车
        return title || t('shortcut_cart');
      case 'personalCenter':
        // 我的
        return title || t('service');
      case 'homePage':
        // 首页
        return title || t('tab_index');
      case 'message':
        // 消息中心
        return title || t('message_center');
      case 'setting':
        // 设置
        return title || t('setting');
      case 'scan':
        // 扫一扫
        return title || t('scan');
      case 'search':
        // 搜索
        return title || t('search');
      case 'userContentCenter':
        // 用户内容中心
        return title || t('userContentCenter');
      case 'share':
        // 分享/分享赚
        return title || t('share');
      case 'custom':
        // 自定义
        return title;
      default:
        break;
    }
  }
  handleIconUrl(url: string, item: any): any {
    const { actionUrl, actionUrlWap } = item;
    if (PlatformUtils.isApp()) {
      return this.handleApkUrl(url, actionUrl);
    } else {
      return this.handleWapUrl(url, actionUrlWap);
    }
  }
  handleApkUrl(url: string, iconUrl: any) {
    const targetRoute = 'SearchDefault';
    let configInfo = {
      searchHotListShow: 'true', // 热搜榜是否显示
      searchHistoryShow: 'true', // 历史记录是否显示
      searchResultPageProdShow: 'true', // 结果页商品是否显示
      searchResultPageActivityShow: 'true', // 结果活动是否显示
      searchResultPageContentShow: 'true', // 结果页内容是否显示
      searchFindShow: 'true',
      relativeWordShow: 'true',
      prodSearchScope: 'all',
      searchScence: '',
    };
    if (this.props.configInfo) {
      configInfo = JSON.parse(this.props.configInfo) || {};
    }
    let apkUrl = `vmall://com.vmall.client/home/rnSearch?targetRoute=${targetRoute}&searchHistoryShow=${configInfo.searchHistoryShow}&searchHotListShow=${configInfo.searchHotListShow}&searchResultPageProdShow=${configInfo.searchResultPageProdShow}&searchResultPageActivityShow=${configInfo.searchResultPageActivityShow}&searchResultPageContentShow=${configInfo.searchResultPageContentShow}`;
    if (!!configInfo.searchFindShow) {
      apkUrl = `${apkUrl}&searchFindShow=${configInfo.searchFindShow}&relativeWordShow=${configInfo.relativeWordShow}&prodSearchScope=${configInfo.prodSearchScope}&searchScence=${configInfo.searchScence}`;
    }

    switch (url) {
      case 'scan':
        return iconUrl || INTERNAL_JUMP_LINK.APP_SCAN_URL;
      case 'cart':
        return iconUrl || INTERNAL_JUMP_LINK.APP_CART_URL;
      case 'personalCenter':
        return iconUrl || INTERNAL_JUMP_LINK.APP_PERSONCENTER_URL;
      case 'message':
        return iconUrl || INTERNAL_JUMP_LINK.APP_MESSAGEURL;
      case 'homePage':
        return iconUrl || INTERNAL_JUMP_LINK.APP_HOMEPAGEURL;
      case 'search':
        return iconUrl || apkUrl;
      case 'setting':
        return iconUrl || INTERNAL_JUMP_LINK.APP_SETTINGURL;
      case 'userContentCenter':
        return iconUrl || INTERNAL_JUMP_LINK.APP_USERCONTENTCENTER_URL;
      case 'custom':
        return iconUrl;
      case 'share':
        return '';
      default:
        break;
    }
  }
  handleWapUrl(url: string, iconUrl: any) {
    const params = {
      targetRoute: 'SearchDefault',
      routeParams: {
        configInfo: encodeURIComponent(this.props.configInfo),
      },
    };
    const searchParams = encodeURIComponent(JSON.stringify(params));
    switch (url) {
      case 'scan':
        return iconUrl || INTERNAL_JUMP_LINK.APP_SCAN_URL;
      case 'cart':
        return iconUrl || `${env.wapDomain}cart`;
      case 'personalCenter': {
        let personalUrl = env.wapDomain + URL_CONSTANTS.PERSONAL_URL_WAP;
        if (Cookies.get('rnpersonalurlwap')) {
          personalUrl = Cookies.get('rnpersonalurlwap');
        } else {
          personalUrl = env.wapDomain + URL_CONSTANTS.PERSONAL_URL_WAP;
        }
        return iconUrl || personalUrl;
      }
      case 'message':
        return iconUrl || `${env.wapDomain}message/index`;
      case 'search':
        return iconUrl || `${env.wapDomain}portal/search/index.html?searchParams=${searchParams}`;
      case 'homePage':
        return iconUrl || `${env.wapDomain}`;
      case 'setting':
        return iconUrl || `${env.wapDomain}setting/index`;
      case 'userContentCenter':
        return iconUrl || `${env.wapDomain}content/index`;
      case 'custom':
        return iconUrl;
      default:
        break;
    }
  }
  handleListType(type: string): any {
    switch (type) {
      case 'scan':
        return '28';
      case 'personalCenter':
        return '23';
      case 'cart':
        return '21';
      case 'homePage':
        return '22';
      case 'message':
        return '10';
      case 'search':
        return '20';
      case 'setting':
        return '9';
      case 'custom':
        return '25';
      case 'userContentCenter':
        return '24';
      default:
        break;
    }
  }
  componentDidUpdate(prevProps) {
    if (this.props.configInfo !== prevProps.configInfo) {
      const { headStyle } = this.props;
      headStyle && headStyle.iconTexts && headStyle.iconTexts.length !== 0
        ? this.handleIconList(headStyle.iconTexts)
        : null;
    }
  }
  getSize = () => {
    return getScreenSize(this.props.width);
  };
  isApp = () => {
    return this.getSize() === 'small';
  };
  // 屏幕尺寸大于1200，并为web平台下，渲染为pad样式
  isPadPc = () => {
    return this.getSize() === 'medium' && this.isPadHorizonta() && this.props.width >= 1024;
  };
  isPad = () => {
    return this.getSize() === 'medium';
  };
  isPadHorizonta = () => {
    const sWidth = PlatformUtils.isWeb()
      ? Dimensions.get('window').width
      : CommonUtils.getWindowSize('personal').screenWidth;
      const sHeight = PlatformUtils.isWeb()
      ? Dimensions.get('window').height
      : CommonUtils.getWindowSize('personal').screenHeight;
    return sWidth >= sHeight;
  };
  // 拉起登录
  goLogin = (actionName) => {
    const url = 'vmall://com.vmall.client/home/login';
    this.props.clickItem(110000101, url, actionName?.includes('昵称') ? 2 : 1);
    EventTracking.execReportData('', true);
    RouterUtils.gotoPage(url);
  };

  userInfoClick = (actionName) => {
    let url;
    const isShow = PlatformUtils.isAndroid() || PlatformUtils.isHarmony() ? 'APP' : 'IOS';
    if (PlatformUtils.isApp()) {
      url = `vmall://com.vmall.client/home/activity?pn=MemberPrivilege${isShow}&isShowLayout=false`;
    }
    this.props.clickItem(110000101, url, actionName?.includes('昵称') ? 2 : 1);
    EventTracking.execReportData('', true);
    if (this.props.enableAdvancedFeature === 0 && !PlatformUtils.isWeb()) {
      return;
    }
    RouterUtils.gotoPage(url);
  };

  getWidth = () => {
    const width: number = CommonUtils.getWindowSize('personal').screenWidth;
    const height: number = CommonUtils.getWindowSize('personal').screenHeight;
    return { width, height };
  };
  getChangeStyle = () => {
    let backGroundStyle = this.getBackgrounStyle();
    const { mergeStyle } = this.props;
    if (mergeStyle?.imgStyle?.backgroundColor) {
      backGroundStyle = null;
      this.setState({
        backGroundStyle,
      });
    } else if (mergeStyle?.bgImg) {
      backGroundStyle = mergeStyle.bgImg;
      this.setState({
        backGroundStyle,
      });
    }
  };

  private getBackgrounStyle() {
    if (this.props.isMember) {
      return this.getMemberBg();
    } else {
      if (ScreenUtils.isMedium(this.getWidth().width)) {
        return ScreenUtils.isPadHorizontal(this.getWidth().width, this.getWidth().height)
          ? ImgArray.oNBgPadT
          : ImgArray.oNBgPadS;
      }
      return ImgArray.oNBg;
    }
  }

  private getMemberBg() {
    if (ScreenUtils.isMedium(this.getWidth().width)) {
      return ScreenUtils.isPadHorizontal(this.getWidth().width, this.getWidth().height)
        ? ImgArray.upBgPad
        : ImgArray.upBgPadS;
    }
    return ImgArray.upBg;
  }

  getIconList = () => {
    const arr: any = [];
    const { iconList } = this.state;
    if (iconList?.length > 0) {
      iconList.map((item: any) => {
        const clickType = Number(item.clickType);
        if (clickType === 28 || clickType === 9 || clickType === 10) {
          arr.push(item);
        }
      });
      arr.sort((a, b) => Number(a.iconNo) - Number(b.iconNo));
    }
    return arr;
  };

  renderNoShowHeader = (_styles, height, top) => {
    return (
      <View
        style={[
          _styles.View,
          {
            height: height,
            paddingTop: top,
          },
        ]}
      />
    );
  };

  renderShowHeader = (
    imgBgUri,
    memberStyle,
    _styles,
    newMergeStyle,
    height,
    top,
    isLogin,
    showText,
    item,
    showIcon,
    avatarIcon,
    marginLeft,
    loginDefaultAvatar,
    unLoginDefaultAvatar,
    mergeStyle,
    unLoginText,
    iconList,
  ) => {
    const { userName, userLevel, isMember } = this.props;
    return (
      <RNImageBackground
        imgUri={imgBgUri}
        imgViewStyle={[memberStyle]}
        style={[
          _styles.View,
          memberStyle,
          newMergeStyle?.imgStyle,
          {
            height,
            paddingTop: top,
          },
        ]}
        isFromPersonal={true}
      >
        <View style={[_styles.avartWrap]}>
          <AnimationHeader
            _styles={_styles}
            mergeStyle={mergeStyle}
            unLoginText={unLoginText}
            newMergeStyle={unLoginText}
            isLogin={isLogin}
            showText={showText}
            item={item}
            showIcon={showIcon}
            avatarIcon={avatarIcon}
            marginLeft={marginLeft}
            userInfoAnimatedValue={this.userInfoAnimatedValue}
            titleAnimatedValue={this.titleAnimatedValue}
            userInfoClick={this.userInfoClick}
            canClick={this.state.canClick}
            loginDefaultAvatar={loginDefaultAvatar}
            unLoginDefaultAvatar={unLoginDefaultAvatar}
            goLogin={this.goLogin}
            userName={userName}
            userLevel={userLevel}
            isMember={isMember}
            avaImg={this.props.avaImg}
          />
        </View>
        <View style={_styles.iconList}>
          {iconList.length > 0 && (
            <IconList
              size={this.getSize()}
              cartNum={this.props.cartNum}
              messageNum={this.props.messageNum}
              style={_styles}
              iconList={iconList}
              mergeStyle={mergeStyle}
              newMergeStyle={newMergeStyle}
              IosStatusBarHeight={iosStatusBarHeight}
              pageCatCode={'p_personalCenter'}
              pageCatName={t('personal')}
              resSiteCode={'s_personalCenter_head'}
              resSiteName={t('top_card')}
              pageId={this.props.pageId}
              openShare={this.openShareDialog}
              getIsLogin={this.getIsLogin}
              shareType={this.shareInfo?.shareType}
            />
          )}
        </View>
      </RNImageBackground>
    );
  };

  render() {
    const { mergeStyle, isLogin, vproList, isMember } = this.props;
    const newMergeStyle = mergeStyle;
    const { showText, item, showIcon, avatarIcon, height, top, imgBgUri, memberStyle } = this.initVariable(
      vproList,
      newMergeStyle,
    );
    const unLoginText = PlatformUtils.isHarmony() ? t('harmonyLogin') : `${t('login')}/${t('register')}`;
    // 登录状态下默认头像
    const loginDefaultAvatar = PlatformUtils.isHarmony() ? ImgArray.harmonyloginAvatar : ImgArray.icAvatar;
    // 未登录状态下默认头像
    const unLoginDefaultAvatar = PlatformUtils.isHarmony() ? ImgArray.harmonyUnloginAvatar : ImgArray.icAvatar;
    let marginLeft = 0;
    marginLeft = this.getMarginLeft(showText, marginLeft, showIcon);
    return (
      <WithTheme themeStyles={(theme) => styles(theme, this.isPad(), this.props.isShow, newMergeStyle, isMember)}>
        {(_styles, theme) => {
          const { changeColor } = this.props;
          // 图标变装颜色
          let mergeStyle = this.handleMergeStyle(newMergeStyle, isMember, theme);
          if (changeColor?.textStyle?.color && !isMember) {
            mergeStyle = changeColor.textStyle.color;
          }
          const iconList = this.getIconList();
          return this.props.isShow ? (
            <>
              {this.renderShowHeader(
                imgBgUri,
                memberStyle,
                _styles,
                newMergeStyle,
                height,
                top,
                isLogin,
                showText,
                item,
                showIcon,
                avatarIcon,
                marginLeft,
                loginDefaultAvatar,
                unLoginDefaultAvatar,
                mergeStyle,
                unLoginText,
                iconList,
              )}
            </>
          ) : (
            <>{this.renderNoShowHeader(_styles, height, iconList)}</>
          );
        }}
      </WithTheme>
    );
  }

  private getMarginLeft(showText: any, marginLeft: number, showIcon: any) {
    if (showText) {
      marginLeft = -5;
    } else if (showIcon) {
      marginLeft = -3;
    }
    return marginLeft;
  }

  private initVariable(vproList: any, newMergeStyle: any) {
    const item = vproList?.configInfo && JSON.parse(vproList.configInfo);
    let showText;
    let showIcon;
    let avatarIcon;
    if (item) {
      showText = item?.showAvatarSetting === '1' && item.avatar !== '';
      showIcon = item?.showAvatarSetting === '2' && item.avatarIcon !== '';
      avatarIcon = item?.avatarIcon;
    }
    const height = PlatformUtils.isIOS() ? 56 + iosStatusBarHeight : 56 + this.props.statusBarHeight;
    const top = PlatformUtils.isIOS() ? iosStatusBarHeight : this.props.statusBarHeight;
    const imgBgUri = this.props.isMember ? null : newMergeStyle?.bgImg;
    let memberStyle = newMergeStyle?.imgStyle?.backgroundColor ? newMergeStyle.imgStyle : {};
    memberStyle = this.props.isMember ? {} : memberStyle;
    return { showText, item, showIcon, avatarIcon, height, top, imgBgUri, memberStyle };
  }

  private handleMergeStyle(newMergeStyle: any, isMember: any, theme) {
    let color = theme.C11.color;
    color = newMergeStyle?.textStyle?.color ? newMergeStyle.textStyle?.color : color;
    return {
      textStyle: {
        color: color,
      },
    };
  }
}
export default componentautoscaling(monitor(dapReportList)(itemExposeHoc(PersonalTitle)));
